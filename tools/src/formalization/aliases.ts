/*!
 * Alias lexicons for concept retrieval, loaded as DATA from each base library's `alias_file`
 * (`paperformalizer.json`). A lexicon bridges the vocabulary-mismatch failure of pure keyword
 * retrieval: a plan may say "ignorability" while the library declaration is named
 * `ConditionalExchangeability` — zero shared tokens, so keyword match alone never surfaces it.
 * Each entry maps a canonical concept to its synonyms and to the library module/file path
 * prefixes where that concept's declarations live.
 *
 * Two consumers (see reuse_retrieval.ts):
 *   1. Query expansion — before scoring, a query's terms are widened with the synonyms of
 *      every matched concept.
 *   2. Module-level fallback — when no indexed declaration scores, the matched concepts'
 *      `modules` point the agent at the right area to search by hand.
 *
 * No library configured with an alias file ⇒ no expansion (plain lexical retrieval).
 * The file shape is `{ "version": 1, "library"?: string, "entries": AliasEntry[] }`; the lexicon
 * shipped for Causalean lives at `tools/data/aliases/causalean.json`. Keep entries
 * high-precision (genuine synonyms only) — a loose alias floods every query with false candidates.
 */
import { readFileSync } from "node:fs";
import { z } from "zod";

const aliasEntrySchema = z.object({
  /** Canonical concept label (human-facing; also a surface form for matching). */
  canonical: z.string().min(1),
  /** Synonyms / alternate phrasings that denote the same concept. */
  aliases: z.array(z.string().min(1)),
  /** Case-sensitive whole-word abbreviations (e.g. `IF`), matched only in their exact case so
   *  an ordinary lowercase word (`if`) does not trigger the concept. */
  abbreviations: z.array(z.string().min(1)).optional(),
  /** Library file/module path prefixes where this concept's decls live. */
  modules: z.array(z.string()),
});

const aliasFileSchema = z.object({
  version: z.literal(1),
  library: z.string().optional(),
  entries: z.array(aliasEntrySchema),
});

export type AliasEntry = z.infer<typeof aliasEntrySchema>;

/** Normalize a surface form / query fragment for matching: lowercase, `_`/`-`→space, collapse ws. */
export function normalizeConcept(s: string): string {
  return s.toLowerCase().replace(/[_\-]+/g, " ").replace(/\s+/g, " ").trim();
}

/** Parse alias-file text; throws naming `file` when it is not JSON or not the alias shape. */
export function parseAliasFileText(text: string, file: string): AliasEntry[] {
  let raw: unknown;
  try {
    raw = JSON.parse(text);
  } catch (e) {
    throw new Error(`alias file ${file} is not JSON (${e instanceof Error ? e.message : String(e)})`);
  }
  const parsed = aliasFileSchema.safeParse(raw);
  if (!parsed.success) {
    const detail = parsed.error.issues.map((i) => `${i.path.join(".") || "(root)"}: ${i.message}`).join("; ");
    throw new Error(`invalid alias file ${file} (${detail})`);
  }
  return parsed.data.entries;
}

/**
 * Load one configured alias file. An unreadable or malformed file THROWS: the owner configured
 * it, and a run that silently lost its lexicon would retrieve worse without anyone knowing.
 * `loadToolkitConfig` validates every configured alias file at start-up, so a run fails before
 * any work rather than mid-stage.
 */
export function loadAliasFile(file: string): AliasEntry[] {
  let text: string;
  try {
    text = readFileSync(file, "utf8");
  } catch (e) {
    throw new Error(`cannot read alias file ${file} (${e instanceof Error ? e.message : String(e)})`);
  }
  return parseAliasFileText(text, file);
}

export interface AliasExpansion {
  /** Extra surface terms (canonical + synonyms of matched concepts) to widen the query. */
  terms: string[];
  /** Module path prefixes suggested by matched concepts (module-level fallback). */
  modules: string[];
  /** Canonical concepts that matched the query (debug / display). */
  concepts: string[];
}

/**
 * Find every entry of `lexicon` whose canonical or any synonym occurs in `text`, and return
 * the union of their surface forms (as expansion terms), suggested modules, and the matched
 * canonical concepts. Single-word forms match on whole-word boundaries; multi-word forms match
 * as substrings; abbreviations match case-sensitively as whole words. Empty lexicon ⇒ empty
 * expansion.
 */
export function expandQuery(text: string, lexicon: readonly AliasEntry[] = []): AliasExpansion {
  const padded = " " + normalizeConcept(text) + " ";
  const terms = new Set<string>();
  const modules = new Set<string>();
  const concepts = new Set<string>();
  for (const e of lexicon) {
    const forms = [e.canonical, ...e.aliases];
    const abbrev = (e.abbreviations ?? []).some((a) =>
      new RegExp(`\\b${a.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`).test(text));
    const hit = abbrev || forms.some((f) => {
      const nf = normalizeConcept(f);
      return nf.includes(" ") ? padded.includes(nf) : padded.includes(" " + nf + " ");
    });
    if (!hit) continue;
    concepts.add(e.canonical);
    for (const f of forms) terms.add(normalizeConcept(f));
    for (const m of e.modules) modules.add(m);
  }
  return { terms: [...terms], modules: [...modules], concepts: [...concepts] };
}
