// The toolkit's topic tree, `<toolkit>/doc/taxonomy.json`: the topic paths a toolkit module may live
// under (`<lib>/<Division>/<topic path>/<File>.lean`). It mirrors Mathlib's top level and is curated
// by the owner: the curator, the study coordinator and the gardener choose among its topics, and a
// new topic enters only as a `new_topic` checklist item the owner accepts. A toolkit without the
// file reads the template's tree (`templates/toolkit/doc/taxonomy.json`); a live promotion writes it
// into the toolkit on first use (`ensureTaxonomy`).
import { existsSync } from "node:fs";
import { mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { writeTextAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "./config.js";
import { toolkitTemplateDir } from "./lakefile.js";

const SEGMENT_RE = /^[A-Z][A-Za-z0-9]*$/;

export const topicSchema = z.object({
  /** `/`-separated UpperCamelCase segments (`Probability/Conditioning`). */
  path: z.string().refine((p) => p.split("/").every((s) => SEGMENT_RE.test(s)), "topic path segments are UpperCamelCase"),
  /** One line: what belongs there. */
  scope: z.string().min(1),
});
export type Topic = z.infer<typeof topicSchema>;

export const taxonomySchema = z.object({
  version: z.literal(1),
  about: z.string().optional(),
  topics: z.array(topicSchema),
}).passthrough();
export type Taxonomy = z.infer<typeof taxonomySchema>;

export function taxonomyPath(cfg: Pick<ToolkitConfig, "toolkitRoot">): string {
  return path.join(cfg.toolkitRoot, "doc", "taxonomy.json");
}

export function templateTaxonomyPath(): string {
  return path.join(toolkitTemplateDir(), "doc", "taxonomy.json");
}

export function parseTaxonomy(text: string, source: string): Taxonomy {
  const r = taxonomySchema.safeParse(JSON.parse(text));
  if (!r.success) throw new Error(`${source}: ${r.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
  return r.data;
}

/** The toolkit's own tree, or null when it has none yet. */
export async function readToolkitTaxonomy(cfg: Pick<ToolkitConfig, "toolkitRoot">): Promise<Taxonomy | null> {
  const p = taxonomyPath(cfg);
  return existsSync(p) ? parseTaxonomy(await readFile(p, "utf8"), p) : null;
}

/** The tree in effect: the toolkit's, else the template's (nothing is written). */
export async function effectiveTaxonomy(cfg: Pick<ToolkitConfig, "toolkitRoot">): Promise<Taxonomy> {
  return (await readToolkitTaxonomy(cfg)) ?? parseTaxonomy(await readFile(templateTaxonomyPath(), "utf8"), templateTaxonomyPath());
}

/** The toolkit's tree, written from the template on first use. */
export async function ensureTaxonomy(cfg: Pick<ToolkitConfig, "toolkitRoot">, log?: (m: string) => void): Promise<Taxonomy> {
  const own = await readToolkitTaxonomy(cfg);
  if (own) return own;
  const tpl = await readFile(templateTaxonomyPath(), "utf8");
  await mkdir(path.dirname(taxonomyPath(cfg)), { recursive: true });
  await writeTextAtomic(taxonomyPath(cfg), tpl);
  log?.(`topic tree: ${taxonomyPath(cfg)} written from the template (edit it only through new_topic decisions)`);
  return parseTaxonomy(tpl, taxonomyPath(cfg));
}

/** Add accepted topics (idempotent) and write the toolkit's tree. */
export async function addTopics(cfg: Pick<ToolkitConfig, "toolkitRoot">, topics: readonly Topic[]): Promise<Taxonomy> {
  const t = await ensureTaxonomy(cfg);
  const have = new Set(t.topics.map((x) => x.path));
  const added = topics.filter((x) => !have.has(x.path));
  if (added.length === 0) return t;
  const next: Taxonomy = { ...t, topics: [...t.topics, ...added].sort((a, b) => a.path.localeCompare(b.path)) };
  await writeTextAtomic(taxonomyPath(cfg), `${JSON.stringify(next, null, 2)}\n`);
  return next;
}

/** The topic path of a toolkit module path (`Toolkit/Foundations/Probability/Conditioning.lean` →
 *  `Probability`), or null when it is not `<lib>/<Division>/<topic…>/<File>.lean`. */
export function topicOfModulePath(rel: string, cfg: Pick<ToolkitConfig, "lib" | "divisions">): string | null {
  const parts = rel.replace(/\\/g, "/").replace(/\.lean$/, "").split("/");
  if (parts[0] !== cfg.lib || !cfg.divisions.includes(parts[1] ?? "") || parts.length < 4) return null;
  return parts.slice(2, -1).join("/");
}

/** Whether a new topic path is well formed: UpperCamelCase segments, at most two levels, and a
 *  second-level topic sits under a topic of the tree. */
export function newTopicProblem(p: string, t: Taxonomy): string | null {
  const segs = p.split("/");
  if (!segs.every((s) => SEGMENT_RE.test(s))) return `new topic "${p}" must be UpperCamelCase segments`;
  if (segs.length > 2) return `new topic "${p}" is deeper than two levels`;
  if (t.topics.some((x) => x.path === p)) return `new topic "${p}" already exists`;
  if (segs.length === 2 && !t.topics.some((x) => x.path === segs[0])) return `new topic "${p}" sits under "${segs[0]}", which is not a topic`;
  return null;
}

/** The tree in words for a prompt: one `- path: scope` line per topic. */
export function taxonomyPromptText(t: Taxonomy): string {
  return t.topics.map((x) => `- ${x.path}: ${x.scope}`).join("\n");
}
