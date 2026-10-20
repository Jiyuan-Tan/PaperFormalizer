/**
 * The REFERENCE core — what the V1 agent actually writes — and its materialization.
 *
 * The agent never types paper text. It names, for every node, WHERE the text is: an
 * environment id from `envs.json` (its body or its proof), optionally narrowed to a slice
 * between two short verbatim anchor phrases, or a slice of the running text (`prose`). The
 * runner copies the text out of the parsed source, so `statement`, `condition`,
 * `construction` and `proof_tex` are verbatim by construction, and the class of failures
 * that came from a model re-typing TeX inside JSON (escaping, tabs, control spaces,
 * punctuation moved across a `$`, footnotes, a slice running into the next environment)
 * cannot occur. What the agent still decides — and what the referee still judges — is the
 * structure: which environments are results, which clauses are hypotheses, the wiring.
 */
import { z } from "zod";
import type { Core } from "../core/schema.js";
import { accountableSites, DISMISSAL_REASONS, joinLocators } from "./inline_citations.js";
import { closingPointAfter, openConstructsAt } from "./tex_balance.js";
import { sentenceSpans } from "./transcription_lint.js";
import type { EnvsJson, TexEnv, TexLocator } from "./types.js";
import { regionUnits } from "./units.js";

/** Two short verbatim phrases; the slice runs from the start of `from` to the end of `to`.
 * `to` may equal `from` (a one-phrase slice). Whitespace inside an anchor is matched
 * loosely; everything else must be exact. */
export const AnchorSliceSchema = z.object({
  from: z.string().min(2),
  to: z.string().min(1),
});
export type AnchorSlice = z.infer<typeof AnchorSliceSchema>;

/** Text taken from an environment: its body (default) or its proof — whole, a run of its
 * numbered sentences (`sentences: [first, last]`, 1-based, inclusive, as numbered in the
 * SCOPE block), or an anchor slice. Sentences need no copying at all; anchors are for a
 * clause inside a sentence. */
export const EnvSourceSchema = z.object({
  env: z.string().min(1),
  region: z.enum(["body", "proof"]).default("body"),
  sentences: z.tuple([z.number().int().min(1), z.number().int().min(1)]).optional(),
  slice: AnchorSliceSchema.optional(),
});

/** Text taken from the running text of the flattened paper, always sliced. */
export const ProseSourceSchema = z.object({
  prose: z.literal(true),
  slice: AnchorSliceSchema,
});

export const SourceRefSchema = z.union([EnvSourceSchema, ProseSourceSchema]);
export type SourceRef = z.infer<typeof SourceRefSchema>;

const StandardTag = z.object({ name: z.string(), cite: z.string() });
const NovelTag = z.object({ flag: z.literal(true), justification: z.string() });

export const RefAssumptionSchema = z.object({
  id: z.string().regex(/^ass:[a-z0-9-]+$/),
  kind: z.string().optional(),
  source: SourceRefSchema,
  free_symbols: z.array(z.string()).optional(),
  constants: z.array(z.string()).optional(),
  standard: StandardTag.optional(),
  novel: NovelTag.optional(),
  used_by: z.array(z.string()).optional(),
});

export const RefDefinitionSchema = z.object({
  id: z.string().regex(/^def:[a-z0-9-]+$/),
  name: z.string().min(1),
  source: SourceRefSchema,
  free_symbols: z.array(z.string()).optional(),
  inputs: z.array(z.string()).optional(),
  by_member_properties: z.array(z.string()).optional(),
});

export const CitedSourceRefSchema = z.object({
  cite: z.string(),
  locator: z.string(),
  verbatim_statement: z.string(),
});

export const RefStatementSchema = z.object({
  id: z.string().regex(/^(thm|lem|prop):[a-z0-9-]+$/),
  kind: z.enum(["theorem", "lemma", "proposition"]),
  /** The environment the result is printed in; the statement is its whole body. */
  env: z.string().min(1),
  status: z.enum(["to-prove", "cited"]).default("to-prove"),
  depends_on: z.array(z.string()).default([]),
  /** Node ids appended as `[Hypotheses: …]`; each must also be in `depends_on`. */
  hypotheses: z.array(z.string()).optional(),
  free_symbols: z.array(z.string()).optional(),
  source: CitedSourceRefSchema.optional(),
});

/**
 * A published result a PROOF invokes by citation (`inline_citations.ts`), made a cited leaf of that
 * proof's result. `site` is the id the INLINE CITATIONS block gives the citation — `sites`, in its
 * place, the ids of the several results ONE citation names, which make one leaf; `units` the first
 * and last of the consecutive proof units (`<env>/proof/<p>/<u>`) holding the citation and the step
 * it gives. The runner copies that passage as the node's text and the work and locator from the
 * site; nobody types the cited result. `cite`: which of the works, when one command cites several.
 */
// TODO: an optional `gives` anchor delimiting, inside `units`, the assertion the cited result gives.
export const ProofCitationSchema = z
  .object({
    id: z.string().regex(/^lem:[a-z0-9-]+$/),
    site: z.string().min(1).optional(),
    sites: z.array(z.string().min(1)).min(1).optional(),
    units: z.tuple([z.string().min(1), z.string().min(1)]),
    cite: z.string().optional(),
    depends_on: z.array(z.string()).default([]),
    free_symbols: z.array(z.string()).optional(),
  })
  .refine((c) => (c.site === undefined) !== (c.sites === undefined), { message: "give `site` (one result) or `sites` (the results one citation names), not both" });

/** A citation with a result locator that is not a use of the result. */
export const DismissedCitationSchema = z.object({
  site: z.string().min(1),
  reason: z.enum(Object.keys(DISMISSAL_REASONS) as [keyof typeof DISMISSAL_REASONS, ...Array<keyof typeof DISMISSAL_REASONS>]),
  note: z.string().default(""),
});

export const RefCoreSchema = z.object({
  qid: z.string(),
  target_estimand: z.string().min(1),
  estimand_functional: z.string().optional(),
  symbols: z.array(z.record(z.unknown())).default([]),
  /** The paper's settings, one entry per setting it works in (what is random, what is fixed, the
   * law): the F stages derive their probability worlds from it. */
  sampling_model: z.record(z.string()).optional(),
  assumptions: z.array(RefAssumptionSchema).default([]),
  definitions: z.array(RefDefinitionSchema).default([]),
  statements: z.array(RefStatementSchema).default([]),
  /** The accounting of the inline citations. Optional, never defaulted: a reference core without
   * either key was written before the accounting existed (`accountsForCitations`). */
  proof_citations: z.array(ProofCitationSchema).optional(),
  dismissed_citations: z.array(DismissedCitationSchema).optional(),
});
export type RefCore = z.infer<typeof RefCoreSchema>;

/** Whether a reference core accounts for the paper's inline citations (one written before the
 * accounting existed does not: its sites are warnings, never violations). */
export function accountsForCitations(ref: Pick<RefCore, "proof_citations" | "dismissed_citations">): boolean {
  return ref.proof_citations !== undefined || ref.dismissed_citations !== undefined;
}

/** Assumption ids the transcription may not use (see `materializeRefCore`). */
export const RESERVED_ASSUMPTION_ID = /^ass:(bk|pin|patch)-/;

/** The `tex_locator` a prose node carries until the runner resolves its lines. */
export const PROSE_LOCATOR: TexLocator = { file: "flat.tex", from: 0, to: 0, env: "prose", label: null };

function escapeRe(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

/** Regex for a verbatim anchor phrase: whitespace inside it is matched loosely, and math
 * delimiters `$` are optional (an anchor typed as `$\mathcal{S}_2 is` still finds
 * `$\mathcal{S}_2$ is`). The SLICE is still cut from the real text, so tolerance here only
 * helps the anchor land; it never alters what is copied. */
function anchorRe(anchor: string): RegExp {
  const tokens = anchor.trim().split(/\s+/).filter((t) => t.length > 0);
  const tok = (t: string): string => escapeRe(t).replace(/\\\$/g, "\\$?");
  return new RegExp(tokens.map(tok).join("\\$?\\s+\\$?"), "g");
}

/** Where `anchor` occurs in `text`, as [start, end) pairs. */
export function anchorMatches(text: string, anchor: string): Array<{ start: number; end: number }> {
  const out: Array<{ start: number; end: number }> = [];
  for (const m of text.matchAll(anchorRe(anchor))) out.push({ start: m.index, end: m.index + m[0].length });
  return out;
}

/**
 * The end of a cut `text[start, end)` that stops just short of closing what it opened: when only
 * whitespace, punctuation and closers (`\]`, `$`, `\end{…}`, `}`) separate `end` from the point
 * where everything is closed, that point — an anchor typed up to a display's last formula ends
 * the slice at the display's closer on the next line. Otherwise `end` unchanged.
 */
export function closedCutEnd(text: string, start: number, end: number): number {
  if (openConstructsAt(text, start, end).length === 0) return end;
  const at = closingPointAfter(text, start, end, Math.min(text.length, end + 200));
  if (at === null) return end;
  const between = text.slice(end, at).replace(/\\[\])]|\$\$?|\\end\s*\{[^{}]*\}|\}/g, "");
  return /^[\s.,;:]*$/.test(between) ? at : end;
}

/**
 * Cut `slice` out of `text`: from the start of a `from` occurrence to the end of the FIRST
 * `to` occurrence after it. When `from` occurs several times, the pair giving the SHORTEST
 * slice is meant (the agent chose `to` for that occurrence); a genuinely ambiguous pair —
 * two occurrences with the same shortest length — is reported. Returns the verbatim slice,
 * or a plain-words reason it cannot be cut.
 */
/** For an anchor that does not occur: the longest run of its words that does, with the
 * source text around it — so the next round can see what the source actually says. */
export function nearestText(text: string, anchor: string): string {
  const words = anchor.trim().split(/\s+/).filter((w) => w.length > 0);
  for (let len = words.length - 1; len >= 1; len -= 1) {
    for (let start = 0; start + len <= words.length; start += 1) {
      const part = words.slice(start, start + len).join(" ");
      const hits = anchorMatches(text, part);
      if (hits.length > 0 && hits.length <= 3) {
        const h = hits[0]!;
        const around = text.slice(Math.max(0, h.start - 40), Math.min(text.length, h.end + 60)).replace(/\s+/g, " ");
        return ` The words "${part}" do occur; the source there reads: …${around}…`;
      }
    }
  }
  return "";
}

export function cutSlice(text: string, slice: AnchorSlice, where: string): { text: string } | { error: string } {
  const froms = anchorMatches(text, slice.from);
  if (froms.length === 0) {
    return { error: `${where}: anchor \`from\` "${slice.from}" does not occur in the source text.${nearestText(text, slice.from)}` };
  }
  const tos = anchorMatches(text, slice.to);
  const candidates: Array<{ start: number; end: number }> = [];
  for (const f of froms) {
    const t = tos.find((m) => m.end >= f.end);
    if (t) candidates.push({ start: f.start, end: t.end });
  }
  if (candidates.length === 0) {
    return {
      error: `${where}: anchor \`to\` "${slice.to}" does not occur after \`from\` "${slice.from}" in the source text.${nearestText(text.slice(froms[0]!.end), slice.to)}`,
    };
  }
  candidates.sort((a, b) => a.end - a.start - (b.end - b.start));
  const best = candidates[0]!;
  if (candidates.length > 1 && candidates[1]!.end - candidates[1]!.start === best.end - best.start && candidates[1]!.start !== best.start) {
    return {
      error: `${where}: anchors "${slice.from}" … "${slice.to}" fit ${candidates.length} places equally well — lengthen \`from\` until the place is unique`,
    };
  }
  return { text: text.slice(best.start, closedCutEnd(text, best.start, best.end)) };
}

/** The numbered sentences of a text, as shown to the agent in the SCOPE block (`"(k) …"`). */
export function numberedSentences(text: string): string[] {
  return sentenceSpans(text).map((sp, k) => `(${k + 1}) ${text.slice(sp.start, sp.end).replace(/\s+/g, " ").trim()}`);
}

export interface Materialized {
  core: Core;
  violations: string[];
}

/**
 * Turn a reference core into a typed core whose every text field is copied verbatim from
 * the parsed source. Structural problems (unknown env, missing proof, anchors that do not
 * cut) come back as `(ref)` violations in the same shape as the lint's, so the agent's next
 * round sees them in one list.
 */
export function materializeRefCore(ref: RefCore, envs: EnvsJson, flatText: string): Materialized {
  const violations: string[] = [];
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));

  const textOf = (
    id: string,
    src: SourceRef,
    field: string,
  ): { text: string; locator: TexLocator; env: TexEnv | null } | null => {
    if ("prose" in src) {
      const cut = cutSlice(flatText, src.slice, `(ref) ${id}.${field}`);
      if ("error" in cut) {
        violations.push(cut.error);
        return null;
      }
      return { text: cut.text, locator: { ...PROSE_LOCATOR }, env: null };
    }
    const env = byId.get(src.env);
    if (!env) {
      violations.push(`(ref) ${id}.${field}: source env "${src.env}" is not an id in envs.json`);
      return null;
    }
    const region = src.region === "proof" ? env.proof : env.body;
    const locator = src.region === "proof" ? env.proofLines : env.lines;
    if (region === null || locator === null) {
      violations.push(`(ref) ${id}.${field}: env "${src.env}" has no proof to take text from`);
      return null;
    }
    if (src.sentences) {
      const spans = sentenceSpans(region);
      const [a, b] = src.sentences;
      if (a > b || b > spans.length) {
        violations.push(`(ref) ${id}.${field}: sentences [${a}, ${b}] out of range — env "${src.env}" ${src.region} has ${spans.length} sentence(s)`);
        return null;
      }
      return { text: region.slice(spans[a - 1]!.start, spans[b - 1]!.end).trim(), locator: { ...locator }, env };
    }
    if (!src.slice) return { text: region.trim(), locator: { ...locator }, env };
    const cut = cutSlice(region, src.slice, `(ref) ${id}.${field}`);
    if ("error" in cut) {
      violations.push(cut.error);
      return null;
    }
    return { text: cut.text, locator: { ...locator }, env };
  };

  const assumptions: Core["assumptions"] = [];
  for (const a of ref.assumptions) {
    // Reserved id families: the referee (`bk`, `pin`) and the fixer (`patch`) mint these on top of
    // the transcription; a transcribed node under one of them would collide with them later.
    if (RESERVED_ASSUMPTION_ID.test(a.id)) {
      violations.push(`(ref) ${a.id}: ids \`ass:bk-*\`, \`ass:pin-*\` and \`ass:patch-*\` are reserved for the referee and the fixer; transcribe the paper's premise under another id`);
      continue;
    }
    const got = textOf(a.id, a.source, "source");
    if (!got) continue;
    const { source: _s, ...rest } = a;
    assumptions.push({ ...rest, condition: got.text, tex_locator: got.locator } as Core["assumptions"][number]);
  }

  const definitions: Core["definitions"] = [];
  for (const d of ref.definitions) {
    const got = textOf(d.id, d.source, "source");
    if (!got) continue;
    const { source: _s, ...rest } = d;
    definitions.push({ ...rest, construction: got.text, tex_locator: got.locator } as Core["definitions"][number]);
  }

  const statements: Core["statements"] = [];
  for (const s of ref.statements) {
    const env = byId.get(s.env);
    if (!env) {
      violations.push(`(ref) ${s.id}.env: "${s.env}" is not an id in envs.json`);
      continue;
    }
    let statement = env.body.trim();
    if (s.hypotheses && s.hypotheses.length > 0) {
      const missing = s.hypotheses.filter((h) => !s.depends_on.includes(h));
      if (missing.length > 0) {
        violations.push(`(ref) ${s.id}.hypotheses: ${missing.join(", ")} listed but not in depends_on`);
      }
      statement = `${statement} [Hypotheses: ${s.hypotheses.join(", ")}]`;
    }
    const { env: _e, hypotheses: _h, source, ...rest } = s;
    const node: Record<string, unknown> = {
      ...rest,
      statement,
      tex_locator: { ...env.lines },
    };
    if (s.status === "cited") {
      if (!source) violations.push(`(ref) ${s.id}: status "cited" needs \`source\` {cite, locator, verbatim_statement}`);
      else node.source = source;
    } else if (env.proof !== null) {
      node.proof_tex = env.proof.trim();
    }
    statements.push(node as Core["statements"][number]);
  }

  // The inline cited leaves: the host's own proof passage, and the edge from the host.
  if (ref.proof_citations && ref.proof_citations.length > 0) {
    const sites = accountableSites(envs, envs.envs.map((e) => e.id));
    for (const c of ref.proof_citations) {
      const bad = (msg: string): void => void violations.push(`(ref) ${c.id}: ${msg}`);
      const ids = c.sites ?? [c.site!];
      const mine = ids.map((id) => sites.find((x) => x.id === id));
      const unknown = ids.filter((_, k) => !mine[k]);
      if (unknown.length > 0) {
        bad(`site ${unknown.map((id) => `"${id}"`).join(", ")} is not a site of INLINE CITATIONS`);
        continue;
      }
      const site = mine[0]!;
      // Several sites make one leaf only as the results of one citation: one proof, one work, one unit.
      if (mine.some((x) => x!.env !== site.env || x!.key !== site.key || !x!.units.some((u) => site.units.includes(u)))) {
        bad(`sites ${ids.map((id) => `"${id}"`).join(", ")} are not the results of one citation — one entry per citation`);
        continue;
      }
      const locator = joinLocators([...new Set(mine.map((x) => x!.locator))]);
      const env = byId.get(site.env)!;
      const hostRef = ref.statements.find((s) => s.env === site.env && s.status !== "cited");
      const host = hostRef && statements.find((s) => s.id === hostRef.id);
      if (!host || !env.proof || !env.proofLines) {
        bad(
          ref.statements.some((s) => s.env === site.env && s.status === "cited")
            ? `${site.env} is a cited result of this core: a citation in its proof needs no entry — remove this one`
            : `no statement node of this core is the result ${site.env} proves`,
        );
        continue;
      }
      if (c.cite === undefined ? site.keys.length > 1 : !site.keys.includes(c.cite)) {
        bad(`the citation names ${site.keys.join(", ")} — set \`cite\` to the one whose ${locator} the proof uses`);
        continue;
      }
      const units = regionUnits(env.proof);
      const [first, last] = c.units.map((id) => units.findIndex((u) => `${site.env}/proof/${u.p}/${u.u}` === id));
      if (first! < 0 || last! < 0 || first! > last!) {
        bad(`units [${c.units.join(", ")}] are not a first and a last unit of the proof of ${site.env}, in order (its units are ${site.env}/proof/<p>/<u>)`);
        continue;
      }
      const text = env.proof.slice(units[first!]!.start, units[last!]!.end).trim();
      const { site: _s, sites: _ss, units: _u, cite, ...rest } = c;
      statements.push({
        ...rest,
        kind: "lemma",
        status: "cited",
        statement: text,
        tex_locator: { ...env.proofLines },
        cited_in: host.id,
        // No `verbatim_statement`: the passage is this paper's text, never the cited work's statement.
        source: { cite: cite ?? site.keys[0]!, locator },
      } as Core["statements"][number]);
      if (!host.depends_on.includes(c.id)) host.depends_on = [...host.depends_on, c.id];
    }
  }

  const core = {
    qid: ref.qid,
    target_estimand: ref.target_estimand,
    ...(ref.estimand_functional ? { estimand_functional: ref.estimand_functional } : {}),
    symbols: ref.symbols,
    ...(ref.sampling_model ? { sampling_model: ref.sampling_model } : {}),
    assumptions,
    definitions,
    statements,
    bibliography: [],
  } as unknown as Core;
  return { core, violations };
}
