/**
 * The F4 seal — `bundle/f4_seal.json`: the two reviewers' F4 receipts of a run under one code.
 *
 * It records, per statement target F4 governs (a delivered node, a tagged symbol cluster), the
 * verdict of each F4 peer and the evidence hash the verdict is bound to (`convergence_evidence.ts`:
 * what Lean elaborated for the target's declarations), and the hash of the paper source. The
 * per-peer receipts of the undelivered and cited targets (`state.json`) are recorded with them, not
 * judged: their gates are F5's and the bank's (`delivery_audit.ts`). `bundle/f4_reviews.log` is what
 * the two peers answered at each F4 pass of the run, as logged; the seal holds its hash, the hash
 * of every file of the bundle's `lean/`, `corrected_paper/` and `page/`, and the arXiv identifier the owner declared
 * (`report --arxiv`; nothing here checks it against the source). `code` is the sha256 of all of it.
 *
 * What a check establishes: the file is whole (the code is its own), it records a pass of both
 * peers on every statement target, and the bundle around it is the one it was written with. It is a
 * checksum, not a signature: everything in it is computed
 * where the run ran, so it shows a submission is consistent with a finished F4, not that F4 ran.
 */
import { createHash } from "node:crypto";
import { lstat, readFile, realpath, stat } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { dualMatchedReceipts, ledgerNodeTargets, REVIEW_STANDARD, symbolVerdictPasses } from "../formalization/convergence_evidence.js";
import { isUndeliveredNode, type FormalizationGraph } from "../graph/types.js";
import type { CitedReviewReceipt, DeliveryReviewReceipt } from "../types.js";

export const F4_SEAL_FILE = "f4_seal.json";
export const F4_REVIEWS_FILE = "f4_reviews.log";
/** `runs/<slug>/<this>`: every reviewer call of the run with the peers' raw output (`proof_reviewer.ts`). */
export const REVIEWER_CALLS_LOG = "logs/_reviewer_calls.log";

/** An arXiv identifier, new or old style, with an optional version. */
export const ARXIV_ID = /^(?:\d{4}\.\d{4,5}|[a-z-]+(?:\.[A-Za-z-]+)?\/\d{7})(?:v\d+)?$/u;
/** A sealed file: under the bundle's `lean/`, `corrected_paper/` (`paper/` in a bundle written before
 *  the folder was renamed) or `page/`, never out of it — plain segments only. */
const SEALED_PATH = /^(?:lean|corrected_paper|paper|page)(?:\/(?!\.{1,2}(?:\/|$))[^/\\\p{Cc}]+)+$/u;

const Receipt = z.object({ verdict: z.string(), evidence_hash: z.string() }).strict();
const Peer = z.enum(["codex", "claude"]);
export const F4SealSchema = z.object({
  version: z.literal(1),
  slug: z.string(),
  paper_sha256: z.string(),
  /** The paper's arXiv identifier as the owner declared it; null when they declared none. */
  arxiv: z.string().regex(ARXIV_ID).nullable(),
  review_standard: z.string(),
  /** The statement targets both peers passed on the same evidence. */
  targets: z.array(z.object({ id: z.string(), codex: Receipt, claude: Receipt }).strict()),
  /** The statement targets that hold no such pass. */
  unreviewed: z.array(z.string()),
  delivery: z.array(z.object({ node_id: z.string(), reviewer: Peer, verdict: z.string(), evidence_hash: z.string() }).strict()),
  cited: z.array(z.object({ node_id: z.string(), reviewer: Peer, check_status: z.string(), cite_id: z.string(), locator: z.string(), evidence_hash: z.string() }).strict()),
  /** sha256 of `f4_reviews.log`; null when the run kept no reviewer log. */
  reviews_sha256: z.string().nullable(),
  /** The files of the bundle's `lean/`, `corrected_paper/` and `page/` (compile outputs apart), by path from the bundle. */
  files: z.array(z.object({ path: z.string().regex(SEALED_PATH), sha256: z.string() }).strict()),
  code: z.string(),
}).strict();
export type F4Seal = z.infer<typeof F4SealSchema>;

/** The code of a seal: sha256 over its fields in a fixed order, so reformatting the file changes nothing. */
function codeOf(s: Omit<F4Seal, "code">): string {
  const receipt = (r: z.infer<typeof Receipt>) => [r.verdict, r.evidence_hash];
  return createHash("sha256").update(JSON.stringify([
    s.version,
    s.slug,
    s.paper_sha256,
    s.review_standard,
    s.targets.map((t) => [t.id, receipt(t.codex), receipt(t.claude)]),
    s.unreviewed,
    s.delivery.map((d) => [d.node_id, d.reviewer, d.verdict, d.evidence_hash]),
    s.cited.map((c) => [c.node_id, c.reviewer, c.check_status, c.cite_id, c.locator, c.evidence_hash]),
    s.reviews_sha256,
    s.arxiv,
    s.files.map((f) => [f.path, f.sha256]),
  ])).digest("hex");
}

export const sha256 = (data: string | Uint8Array): string => createHash("sha256").update(data).digest("hex");

/** The F4 passes of a run's reviewer log (`REVIEWER_CALLS_LOG`): each convergence call with both
 *  peers' raw output, the F2.5 delta calls left out, and every path in `machine` blanked. Pure. */
export function f4Reviews(log: string, machine: readonly string[] = []): string {
  return blankPaths(log.split(/^(?====== reviewer )/mu).filter((s) => s.startsWith("===== reviewer convergence/")).join(""), machine);
}

/** `text` with every path in `machine` blanked. Pure. */
export function blankPaths(text: string, machine: readonly string[]): string {
  // a path, never the start of a longer name beside it
  for (const p of [...new Set(machine)].filter((m) => m.length > 1).sort((a, b) => b.length - a.length)) {
    text = text.replace(new RegExp(`${p.replace(/[.*+?^${}()|[\]\\]/gu, "\\$&")}(?![\\w.-])`, "gu"), "<local>");
  }
  return text;
}

/** What stands beside a seal in its bundle: the reviews file (null: none) and the hash of each file
 *  of `lean/`, `corrected_paper/` and `page/` by its path from the bundle. */
export interface SealedBundle {
  reviews: string | null;
  files: ReadonlyMap<string, string>;
}

/** `seal` bound to the bundle it travels with. Pure. */
export function withBundle(seal: F4Seal, beside: SealedBundle): F4Seal {
  const { code: _c, ...body } = {
    ...seal,
    reviews_sha256: beside.reviews === null ? null : sha256(beside.reviews),
    files: [...beside.files].map(([p, h]) => ({ path: p, sha256: h })).sort(byKey((f) => f.path)),
  };
  return { ...body, code: codeOf(body) };
}

/** The files a seal names, to hash beside it; none when `seal` is no seal. Pure. */
export function sealedPaths(seal: unknown): string[] {
  const parsed = F4SealSchema.safeParse(seal);
  return parsed.success ? parsed.data.files.map((f) => f.path) : [];
}

const byKey = <T>(key: (x: T) => string) => (a: T, b: T): number => (key(a) < key(b) ? -1 : key(a) > key(b) ? 1 : 0);

/** The seal of a run as its records stand. Pure. */
export function buildF4Seal(a: {
  slug: string;
  paperSha256: string;
  graph: FormalizationGraph;
  arxiv?: string | null;
  delivery?: readonly DeliveryReviewReceipt[];
  cited?: readonly CitedReviewReceipt[];
}): F4Seal {
  const dual = dualMatchedReceipts(a.graph.convergenceReview ?? {});
  const byId = new Map(a.graph.nodes.map((n) => [n.id, n] as const));
  // What F5 audits (`auditConvergenceReview`): the delivered node targets, each `matched`, and the
  // tagged symbol clusters, each passed. An untagged symbol has no member to review.
  const nodes = ledgerNodeTargets(a.graph).filter((id) => !isUndeliveredNode(byId.get(id)!));
  const symbols = Object.entries(a.graph.symbolReview ?? {}).filter(([, r]) => !/untagged/iu.test(r.verdict));
  const governed = [...nodes, ...symbols.map(([id]) => id)];
  const cleared = new Set([
    ...nodes.filter((id) => byId.get(id)!.review.status === "matched"),
    ...symbols.filter(([, r]) => symbolVerdictPasses(r.verdict)).map(([id]) => id),
  ].filter((id) => id in dual));
  const body = {
    version: 1 as const,
    slug: a.slug,
    paper_sha256: a.paperSha256,
    arxiv: a.arxiv ?? null,
    review_standard: REVIEW_STANDARD,
    targets: [...cleared]
      .map((id) => ({ id, codex: { verdict: dual[id]!.codex!.verdict, evidence_hash: dual[id]!.codex!.evidence_hash }, claude: { verdict: dual[id]!.claude!.verdict, evidence_hash: dual[id]!.claude!.evidence_hash } }))
      .sort(byKey((t) => t.id)),
    unreviewed: governed.filter((id) => !cleared.has(id)).sort(),
    delivery: (a.delivery ?? [])
      .map((d) => ({ node_id: d.node_id, reviewer: d.reviewer, verdict: d.verdict, evidence_hash: d.evidence_hash }))
      .sort(byKey((d) => `${d.node_id}\u0000${d.reviewer}`)),
    cited: (a.cited ?? [])
      .map((c) => ({ node_id: c.node_id, reviewer: c.reviewer, check_status: c.check_status, cite_id: c.cite_id, locator: c.locator, evidence_hash: c.evidence_hash }))
      .sort(byKey((c) => `${c.node_id}\u0000${c.reviewer}\u0000${c.cite_id}\u0000${c.locator}`)),
    reviews_sha256: null,
    files: [],
  };
  return { ...body, code: codeOf(body) };
}

/** What keeps `seal` (a parsed `f4_seal.json`) from certifying a finished F4; empty when nothing does.
 *  `beside` is the bundle around it, checked when given: the reviews file and every file the seal
 *  names are the ones it was written with. A file it does not name (a build output) is not its
 *  concern. Pure. */
export function checkF4Seal(seal: unknown, beside?: SealedBundle): string[] {
  const parsed = F4SealSchema.safeParse(seal);
  if (!parsed.success) return [`not an F4 seal: ${parsed.error.issues.map((i) => `${i.path.join(".") || "(root)"}: ${i.message}`).join("; ")}`];
  const { code, ...body } = parsed.data;
  const problems: string[] = [];
  if (codeOf(body) !== code) problems.push("the code is not the hash of the seal's contents: the file was changed after it was written");
  if (body.targets.length === 0) problems.push("no target carries a pass of both reviewers");
  for (const t of body.targets) {
    if (t.codex.verdict !== "matched" || t.claude.verdict !== "matched") problems.push(`${t.id}: not passed by both reviewers (codex: ${t.codex.verdict}, claude: ${t.claude.verdict})`);
    else if (t.codex.evidence_hash !== t.claude.evidence_hash) problems.push(`${t.id}: the two reviewers passed different statements`);
  }
  if (body.unreviewed.length > 0) problems.push(`not passed by both reviewers: ${body.unreviewed.join(", ")}`);
  if (!beside) return problems;
  const { reviews } = beside;
  if (body.reviews_sha256 !== null) {
    if (reviews === null) problems.push(`${F4_REVIEWS_FILE} is missing: the seal names the reviews it was written with`);
    else if (sha256(reviews) !== body.reviews_sha256) problems.push(`${F4_REVIEWS_FILE} is not the file the seal was written with`);
  } else if (reviews !== null) problems.push(`${F4_REVIEWS_FILE} is not named by the seal: it was added afterwards`);
  const missing = body.files.filter((f) => !beside.files.has(f.path)).map((f) => f.path);
  const changed = body.files.filter((f) => beside.files.has(f.path) && beside.files.get(f.path) !== f.sha256).map((f) => f.path);
  const some = (paths: string[]): string => `${paths.slice(0, 8).join(", ")}${paths.length > 8 ? `, and ${paths.length - 8} more` : ""}`;
  if (missing.length > 0) problems.push(`missing from the bundle: ${some(missing)}`);
  if (changed.length > 0) problems.push(`changed after the seal was written: ${some(changed)}`);
  return problems;
}

export const SEAL_USAGE =
  "Usage: paperformalizer seal <bundle dir | f4_seal.json>\n" +
  "  check a bundle's F4 seal: the code is the hash of its contents, both reviewers passed every statement target,\n" +
  "  and f4_reviews.log and the files it names (lean/, corrected_paper/, page/) are the ones it was written with.";

/** `paperformalizer seal <path>`: print the code and the verdict; throws when the seal does not hold. */
export async function runSealCli(argv: string[], deps: { log?: (m: string) => void } = {}): Promise<void> {
  const log = deps.log ?? ((m: string) => console.log(m));
  if (argv.length !== 1 || argv[0]!.startsWith("--")) throw new Error(SEAL_USAGE);
  const given = path.resolve(argv[0]!);
  let file = given;
  let seal: unknown;
  try {
    if ((await stat(given)).isDirectory()) file = path.join(given, F4_SEAL_FILE);
    seal = JSON.parse(await readFile(file, "utf8"));
  } catch (err) {
    throw new Error(`cannot read the seal at ${file}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const dir = path.dirname(file);
  const files = new Map<string, string>();
  // Only a regular file of the bundle itself is read: a link, or a path through one, counts as missing.
  const root = await realpath(dir);
  for (const p of sealedPaths(seal)) {
    const full = path.join(dir, p);
    const plain = await lstat(full).then(async (st) => st.isFile() && (await realpath(full)) === path.join(root, p), () => false);
    if (plain) files.set(p, sha256(await readFile(full)));
  }
  const problems = checkF4Seal(seal, { reviews: await readFile(path.join(dir, F4_REVIEWS_FILE), "utf8").catch(() => null), files });
  if (problems.length > 0) throw new Error(`the F4 seal at ${file} does not hold:\n${problems.map((p) => `  - ${p}`).join("\n")}`);
  const s = seal as F4Seal;
  log(`F4 seal holds: ${s.targets.length} statement target(s) passed by both reviewers${s.delivery.length + s.cited.length > 0 ? ` (and ${s.delivery.length} delivery, ${s.cited.length} cited receipt(s) recorded, not judged)` : ""}; ${s.reviews_sha256 ? `${F4_REVIEWS_FILE} and` : "no reviews file;"} ${s.files.length} file(s) it names (${[...new Set(s.files.map((f) => `${f.path.split("/")[0]}/`))].join(", ")}) are the ones it was written with — ${s.slug}${s.arxiv ? `, arXiv:${s.arxiv} (as declared)` : ""}, code ${s.code}`);
}
