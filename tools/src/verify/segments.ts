/**
 * Segmentation fallback for V1 — the model POINTS at what the parser missed.
 *
 * LaTeX has no grammar for "a theorem" or "a proof": amsthm environments are a convention,
 * and every paper uses a different subset of the alternatives (results in running text,
 * self-defined proof macros, restatements, part labels, proof sections). The deterministic
 * parser (`tex_envs.ts`) covers the common shapes and never drops anything silently — every
 * result or proof it could not place is a warning. When such a GAP warning appears, a small
 * agent pass reads the flat source with line numbers and writes `discovery/segments.json`:
 * flat LINE RANGES for the results the parser missed and for the proofs it could not attach.
 * This module validates that file and materializes it into `EnvsJson` — verbatim from the
 * source, exactly as the parser would have. The contract is the reference core's: the model
 * says WHERE, the program copies. Once written, the file is re-applied deterministically on
 * every `--resume`; no second agent call.
 */
import { z } from "zod";
import type { EnvKind, EnvsJson, TexEnv, TexLocator } from "./types.js";
import { FURTHER_PROOF_SEPARATOR, refsIn, type FlatTex } from "./tex_envs.js";
import { texBalanceProblems } from "./tex_balance.js";

export const V1_SEGMENTS_FILE = "discovery/segments.json";

const LineRangeSchema = z.tuple([z.number().int().min(1), z.number().int().min(1)]);

const SEGMENT_KINDS = ["theorem", "lemma", "proposition", "corollary", "assumption", "definition"] as const;

export const SegmentResultSchema = z.object({
  /** optional handle; else the `\label` in the range, else `<kind>-seg-N` */
  id: z.string().min(1).optional(),
  kind: z.enum(SEGMENT_KINDS),
  /** printed head, e.g. `Theorem 3.1`; becomes the env's `title` */
  printed: z.string().min(1).optional(),
  /** flat line range of the STATEMENT, 1-based inclusive, opener included */
  lines: LineRangeSchema,
  /** flat line range of its proof, when the paper gives one the parser has not attached */
  proof_lines: LineRangeSchema.nullable().optional(),
  note: z.string().optional(),
});

export const SegmentBindingSchema = z.object({
  /** id of a parsed environment (as listed in the PARSED block) */
  result: z.string().min(1),
  /** flat line range of a proof the parser left unattached */
  proof_lines: LineRangeSchema,
  note: z.string().optional(),
});

export const SegmentExtendSchema = z.object({
  /** id of a parsed environment whose statement the parser ended too early */
  env: z.string().min(1),
  /** flat line range the STATEMENT actually spans (it must contain the parsed range) */
  lines: LineRangeSchema,
  note: z.string().optional(),
});

export const SegmentsSchema = z.object({
  results: z.array(SegmentResultSchema),
  bindings: z.array(SegmentBindingSchema),
  extend: z.array(SegmentExtendSchema).optional().default([]),
});
export type Segments = z.infer<typeof SegmentsSchema>;

/** Parser warnings that mean a result or proof exists in the source and was not placed. */
const GAP_RE = [
  /is attached to no result/,
  /not bound — say which it proves/,
  /is commentary, not a proof/,
];

/** The parser warnings that call for the segmentation pass, in order. Empty = parser
 * output is complete as far as it can tell. A scope with no theorem-like environment at
 * all is a gap too (a paper whose results all live in running text the parser did not
 * recognise), reported as one synthetic line. */
export function segmentationGaps(parserWarnings: readonly string[], envs: EnvsJson, theoremLike: readonly string[]): string[] {
  const gaps = parserWarnings.filter((w) => GAP_RE.some((re) => re.test(w)));
  if (theoremLike.length === 0) {
    gaps.unshift(
      `no theorem-like environment was found among the ${envs.envs.length} parsed environment(s); ` +
        `the paper's results must be stated in a form the parser does not recognise`,
    );
  }
  return gaps;
}

/** Flat line range (1-based inclusive) of a parsed environment, for the PARSED block: the
 * parser stores ORIGINAL-file locators, the agent reads the numbered FLAT text. */
export function flatRangeOf(loc: TexLocator, flat: FlatTex): [number, number] | null {
  let from = -1;
  let to = -1;
  flat.lineMap.forEach((m, i) => {
    if (m.file !== loc.file) return;
    if (m.line === loc.from && from < 0) from = i + 1;
    if (m.line === loc.to) to = i + 1;
  });
  return from > 0 && to >= from ? [from, to] : null;
}

function locatorFor(range: [number, number], flat: FlatTex, env: string, label: string | null): TexLocator {
  const a = flat.lineMap[range[0] - 1]!;
  const b = flat.lineMap[range[1] - 1]!;
  return { file: a.file, from: a.line, to: b.file === a.file ? b.line : a.line, env, label };
}

/** A range that is exactly one `\begin{X}[title]…\end{X}` environment yields its BODY, as the
 * parser does for the environments it knows — the agent points at the whole environment. */
export function unwrapEnv(text: string): { body: string; title: string | null } {
  const m = /^\\begin\s*\{([^{}]+)\}\s*(?:\[([^\]]*)\])?([\s\S]*)\\end\s*\{\1\}$/.exec(text.trim());
  if (!m) return { body: text.trim(), title: null };
  return { body: m[3]!.trim(), title: m[2]?.trim() || null };
}

function sliceLines(flat: FlatTex, range: [number, number]): string {
  return unwrapEnv(
    flat.text
      .split("\n")
      .slice(range[0] - 1, range[1])
      .join("\n"),
  ).body;
}

/**
 * Validate `seg` against the parsed environments and the flat text; on success return the
 * environments extended by the segmented results and bindings, plus one note per change
 * (for the referee's parser-warning list). Violations name the entry and are complete
 * (every problem, not just the first) so one revise round can fix them all.
 */
export function applySegments(
  seg: Segments,
  envs: EnvsJson,
  flat: FlatTex,
): { envs: EnvsJson; violations: string[]; notes: string[] } {
  const violations: string[] = [];
  const notes: string[] = [];
  const lineCount = flat.lineMap.length;
  const theoremEnvNames = Object.keys(envs.newtheorem);
  const beginResultRe = new RegExp(String.raw`\\begin\s*\{(${theoremEnvNames.map((n) => n.replace(/\*/g, "\\*")).join("|")})\}`);

  const checkRange = (what: string, r: [number, number]): boolean => {
    if (r[0] > r[1]) {
      violations.push(`(segment) ${what}: lines [${r[0]}, ${r[1]}] run backwards`);
      return false;
    }
    if (r[1] > lineCount) {
      violations.push(`(segment) ${what}: lines [${r[0]}, ${r[1]}] exceed the source (${lineCount} lines)`);
      return false;
    }
    return true;
  };
  /** A range must hold whole TeX: one that starts or ends inside a display, a math span or an
   * environment is a cut, not a statement or a proof. */
  const whole = (what: string, r: [number, number], text: string): boolean => {
    const probs = texBalanceProblems(text);
    if (probs.length === 0) return true;
    violations.push(`(segment) ${what}: lines [${r[0]}, ${r[1]}] cut inside TeX — ${probs.join("; ")}; widen the range to the whole display or environment`);
    return false;
  };

  const out: TexEnv[] = envs.envs.map((e) => ({ ...e }));
  const byId = new Map(out.map((e) => [e.id, e] as const));
  const used = new Set(out.map((e) => e.id));
  const ordinal: Partial<Record<EnvKind, number>> = {};

  seg.results.forEach((r, k) => {
    const what = `results[${k}]${r.id ? ` (${r.id})` : ""}`;
    if (!checkRange(what, r.lines)) return;
    const body = sliceLines(flat, r.lines);
    if (!body) {
      violations.push(`(segment) ${what}: lines [${r.lines[0]}, ${r.lines[1]}] are blank`);
      return;
    }
    if (!whole(what, r.lines, body)) return;
    if (theoremEnvNames.length > 0 && beginResultRe.test(body)) {
      violations.push(
        `(segment) ${what}: lines [${r.lines[0]}, ${r.lines[1]}] contain a \\begin{…} of an environment the parser already ` +
          `extracts; a segment is only for text OUTSIDE every parsed environment`,
      );
      return;
    }
    let proof: string | null = null;
    let proofLines: TexLocator | null = null;
    if (r.proof_lines) {
      if (!checkRange(`${what}.proof_lines`, r.proof_lines)) return;
      if (r.proof_lines[0] <= r.lines[1] && r.proof_lines[1] >= r.lines[0]) {
        violations.push(`(segment) ${what}: proof_lines overlap the statement lines`);
        return;
      }
      proof = sliceLines(flat, r.proof_lines);
      if (!proof) {
        violations.push(`(segment) ${what}: proof_lines [${r.proof_lines[0]}, ${r.proof_lines[1]}] are blank`);
        return;
      }
      if (!whole(`${what}.proof_lines`, r.proof_lines, proof)) return;
      proofLines = locatorFor(r.proof_lines, flat, "segment-proof", null);
    }
    const label = /\\label\s*\{([^{}]*)\}/.exec(body)?.[1]?.trim() ?? null;
    const n = (ordinal[r.kind] ?? 0) + 1;
    ordinal[r.kind] = n;
    // the agent may hand back the paper's label with spaces and colons; a handle is a slug
    const slug = (x: string): string => x.toLowerCase().replace(/[^a-z0-9:_.-]+/g, "-").replace(/^-+|-+$/g, "") || `${r.kind}-seg-${n}`;
    let id = r.id ? slug(r.id) : (label ?? `${r.kind}-seg-${n}`);
    if (used.has(id)) {
      violations.push(`(segment) ${what}: id "${id}" is already taken by a parsed environment; choose another`);
      return;
    }
    used.add(id);
    const env: TexEnv = {
      id,
      kind: r.kind,
      envName: "segment",
      label,
      title: r.printed ?? null,
      body,
      proof,
      proofLines,
      lines: locatorFor(r.lines, flat, "segment", label),
      refs: refsIn(proof ? `${body}\n${proof}` : body),
    };
    out.push(env);
    byId.set(id, env);
    notes.push(
      `segment: ${r.printed ?? r.kind} at flat lines ${r.lines[0]}–${r.lines[1]} read as ${r.kind} "${id}"` +
        (proof ? ` with its proof at ${r.proof_lines![0]}–${r.proof_lines![1]}` : "") +
        (r.note ? ` — ${r.note}` : ""),
    );
  });

  seg.bindings.forEach((b, k) => {
    const what = `bindings[${k}] (${b.result})`;
    const env = byId.get(b.result);
    if (!env) {
      violations.push(`(segment) ${what}: "${b.result}" is not the id of a parsed or segmented environment`);
      return;
    }
    if (!checkRange(what, b.proof_lines)) return;
    const text = sliceLines(flat, b.proof_lines);
    if (!text) {
      violations.push(`(segment) ${what}: proof_lines [${b.proof_lines[0]}, ${b.proof_lines[1]}] are blank`);
      return;
    }
    if (!whole(what, b.proof_lines, text)) return;
    if (env.proof) {
      env.proof = `${env.proof}${FURTHER_PROOF_SEPARATOR}${text}`;
      notes.push(`segment: proof at flat lines ${b.proof_lines[0]}–${b.proof_lines[1]} appended to ${env.id}'s proof` + (b.note ? ` — ${b.note}` : ""));
    } else {
      env.proof = text;
      env.proofLines = locatorFor(b.proof_lines, flat, "segment-proof", null);
      notes.push(`segment: proof at flat lines ${b.proof_lines[0]}–${b.proof_lines[1]} bound to ${env.id}` + (b.note ? ` — ${b.note}` : ""));
    }
    env.refs = refsIn(`${env.body}\n${env.proof}`);
  });

  seg.extend.forEach((x, k) => {
    const what = `extend[${k}] (${x.env})`;
    const env = byId.get(x.env);
    if (!env) {
      violations.push(`(segment) ${what}: "${x.env}" is not the id of a parsed environment`);
      return;
    }
    if (!checkRange(what, x.lines)) return;
    const cur = flatRangeOf(env.lines, flat);
    if (!cur || x.lines[0] > cur[0] || x.lines[1] < cur[1]) {
      violations.push(`(segment) ${what}: lines [${x.lines[0]}, ${x.lines[1]}] must contain the parsed range ${cur ? `[${cur[0]}, ${cur[1]}]` : "(unknown)"}`);
      return;
    }
    const slice = flat.text.split("\n").slice(x.lines[0] - 1, x.lines[1]).join("\n");
    // the statement keeps its parsed start (the opener is not part of the body); only the end moves
    const head = env.body.slice(0, Math.min(60, env.body.length));
    const at = slice.indexOf(head);
    if (at < 0) {
      violations.push(`(segment) ${what}: the extended range does not contain the parsed statement's opening text`);
      return;
    }
    const body = slice.slice(at).trim();
    if (body.length <= env.body.length) {
      violations.push(`(segment) ${what}: the extended range adds nothing to the parsed statement`);
      return;
    }
    if (!whole(what, x.lines, body)) return;
    env.body = body;
    env.lines = { ...env.lines, to: flat.lineMap[x.lines[1] - 1]!.file === env.lines.file ? flat.lineMap[x.lines[1] - 1]!.line : env.lines.to };
    env.refs = refsIn(env.proof ? `${env.body}\n${env.proof}` : env.body);
    notes.push(`segment: ${env.id} extended to flat line ${x.lines[1]} (the parser ended it early)` + (x.note ? ` — ${x.note}` : ""));
  });

  // document order, as the parser would have produced
  const startOf = (e: TexEnv): number => flatRangeOf(e.lines, flat)?.[0] ?? Number.MAX_SAFE_INTEGER;
  out.sort((a, b) => startOf(a) - startOf(b));
  if (seg.results.length === 0 && seg.bindings.length === 0 && seg.extend.length === 0) notes.push("segment: the agent found nothing to add — the gaps are not results or proofs of this paper");
  return { envs: { ...envs, envs: out }, violations, notes };
}

/** The flat text with 1-based line numbers, as the segmenting agent reads it. */
export function numberedFlat(flat: FlatTex): string {
  return flat.text
    .split("\n")
    .map((l, i) => `${String(i + 1).padStart(5)}| ${l}`)
    .join("\n");
}

/**
 * A reference violation whose anchor DOES occur in the source shortly after the environment
 * it was aimed at is a truncated statement: the parser ended the environment early (a
 * paragraph break inside a statement, a shape the boundary rules do not know). One gap line
 * per such environment, for the segmenter to `extend`.
 */
export function truncationGaps(
  violations: readonly string[],
  envOfNode: (nodeId: string) => string | undefined,
  envs: EnvsJson,
  flat: FlatTex,
  anchorMatches: (text: string, anchor: string) => Array<{ start: number; end: number }>,
): string[] {
  const lines = flat.text.split("\n");
  const lineStart: number[] = [0];
  for (const l of lines) lineStart.push(lineStart[lineStart.length - 1]! + l.length + 1);
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));
  const out = new Map<string, string>();
  for (const v of violations) {
    const m = /^\(ref\) ([a-z]+:[A-Za-z0-9_-]+)(?:\.[^:]*)?: anchor `(?:from|to)` "((?:[^"\\]|\\.)*)" does not occur/.exec(v);
    if (!m) continue;
    const envId = envOfNode(m[1]!);
    const env = envId ? byId.get(envId) : undefined;
    if (!env || out.has(env.id)) continue;
    const range = flatRangeOf(env.lines, flat);
    if (!range) continue;
    const endOffset = lineStart[range[1]]!; // start of the line after the environment
    const hit = anchorMatches(flat.text.slice(endOffset, endOffset + 4000), m[2]!)[0];
    if (!hit) continue;
    const hitLine = lineStart.findIndex((s0) => s0 > endOffset + hit.start); // 1-based line of the hit
    out.set(
      env.id,
      `${env.id} (${env.title ?? env.kind}, flat lines ${range[0]}–${range[1]}) appears to end early: the phrase "${m[2]!.slice(0, 60)}" ` +
        `that a node points at occurs at flat line ${hitLine}, after the environment's end — if the statement continues there, \`extend\` it`,
    );
  }
  return [...out.values()];
}
