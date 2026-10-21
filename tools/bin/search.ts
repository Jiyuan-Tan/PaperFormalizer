import { resolve } from "node:path";
import { createRetrieval, type Query, type SearchOpts, type SemanticChannel } from "../src/formalization/reuse_retrieval.js";
import { loadSemanticTier, embedQueries } from "../src/formalization/semantic_tier.js";
import { poolModules } from "../src/formalization/module_tier.js";
import { indexSourceFromPath, indexSourcesFromToolkit, type IndexSource } from "../src/library/sources.js";
import { loadToolkitConfig } from "../src/toolkit/config.js";

/**
 * Search CLI over one or more per-declaration library indices (reuse_retrieval.ts) — the same
 * engine the F1 reuse brief uses. Every hit is tagged with its library.
 *
 *   npx tsx bin/search.ts [sources] <concept words...>      # concept mode (default)
 *   npx tsx bin/search.ts [sources] --type "<pattern>"      # loogle-style symbol match
 *   npx tsx bin/search.ts [sources] --goal "<goal type>"    # goal-directed (F3 mode)
 *   npx tsx bin/search.ts [sources] --scope module "<words>" # module/file-level orientation search
 *
 * Sources: `--index <path>` (repeatable; an index file at any path, library name taken from its
 * modules) OR `--toolkit <path>` (every index `paperformalizer.json` names, plus the toolkit's own).
 * With neither, the toolkit is resolved from PAPERFORMALIZER_TOOLKIT or the cwd.
 * Flags: --k <N>  --scope decl|module|file  --semantic (blend each source's embedding tier when
 * present)  --fusion rrf|weighted (lexical+semantic fusion; default rrf).
 */

const argv = process.argv.slice(2);
const die = (msg: string): never => {
  console.error(msg);
  process.exit(1);
};
const flag = (name: string): string | undefined => {
  const i = argv.indexOf(name);
  if (i < 0) return undefined;
  const v = argv[i + 1];
  if (v === undefined) die(`${name} needs a value.`);
  argv.splice(i, 2);
  return v;
};
const flagAll = (name: string): string[] => {
  const out: string[] = [];
  for (let v = flag(name); v !== undefined; v = flag(name)) out.push(v);
  return out;
};
const boolFlag = (name: string): boolean => {
  const i = argv.indexOf(name);
  if (i < 0) return false;
  argv.splice(i, 1);
  return true;
};
const useSemantic = boolFlag("--semantic");

const fusionArg = flag("--fusion");
if (fusionArg !== undefined && fusionArg !== "rrf" && fusionArg !== "weighted") die(`--fusion must be rrf|weighted (got "${fusionArg}").`);
const fusion = fusionArg as "rrf" | "weighted" | undefined;

// `npm run search` runs in tools/; resolve user paths against the directory it was invoked from.
const userCwd = process.env.INIT_CWD ?? process.cwd();
const indexArgs = flagAll("--index").map((p) => resolve(userCwd, p));
const toolkitArg = flag("--toolkit");
if (indexArgs.length > 0 && toolkitArg !== undefined) die("--index and --toolkit are mutually exclusive.");
let sources: IndexSource[];
if (indexArgs.length > 0) {
  sources = indexArgs.map((p) => indexSourceFromPath(p));
} else {
  let cfg;
  try {
    cfg = loadToolkitConfig({ explicit: toolkitArg ?? null, cwd: userCwd });
  } catch (e) {
    die(`${(e as Error).message}\n(or pass --index <path to a library index>)`);
  }
  sources = indexSourcesFromToolkit(cfg!);
  if (sources.length === 0) die(`${cfg!.configPath} names no existing index.`);
}

const kRaw = flag("--k");
const k = kRaw === undefined ? 8 : Number(kRaw);
if (!Number.isInteger(k) || k < 1) die(`--k must be a positive integer (got "${kRaw}").`);
const typePattern = flag("--type");
const goal = flag("--goal");
const scopeArg = flag("--scope") ?? "decl";
if (scopeArg !== "decl" && scopeArg !== "module" && scopeArg !== "file") die(`--scope must be decl|module|file (got "${scopeArg}").`);
const unknown = argv.find((a) => a.startsWith("--"));
if (unknown) die(`unknown flag ${unknown}`);
const positional = argv.join(" ").trim();

const r = createRetrieval(sources);
if (r.libraries.length === 0) die(`No usable index among: ${sources.map((s) => s.indexPath).join(", ")}`);

/** Scope banner: the costliest misreading of this tool is "no hit ⇒ the fact does not exist". */
const scopeLine =
  `scope: ${r.libraries.map((l) => l.name).join(", ")} only — anything else (e.g. Mathlib) is NOT indexed here; ` +
  "a miss is NOT evidence a fact is missing. Check Mathlib (lean_leansearch / lean_loogle) before concluding absence.";
const header = (mode: string, extra: string, shown: number): string =>
  `${r.libraries.map((l) => `${l.name} @ ${l.library.commit.slice(0, 7)} (${l.library.entries.length} decls)`).join(" · ")}` +
  ` · mode=${mode}${extra} · showing ${shown}/${k}`;

/** Per-library semantic channels for `text` (skipped silently for a source with no embeddings). */
function semanticChannels(text: string, required: boolean): Map<string, SemanticChannel> {
  const channels = new Map<string, SemanticChannel>();
  for (const lib of r.libraries) {
    const tier = loadSemanticTier(lib.source);
    if (!tier) continue;
    try {
      const [queryVec] = embedQueries([text], lib.source);
      channels.set(lib.name, { tier, queryVec });
    } catch (e) {
      console.error(`${lib.name}: query embedding failed (${(e as Error).message}); lexical only.`);
    }
  }
  if (required && channels.size === 0) console.error("--semantic: no source has usable embeddings; lexical only.");
  return channels;
}

if (scopeArg === "module" || scopeArg === "file") {
  // Module/file-level orientation — "which area do I read?" rather than "which lemma?". Ranks
  // modules by the MEAN of each module's top-3 member-decl scores from the fused decl search,
  // with the module `/-! -/` overview + a few prototype ("e.g.") member decls.
  if (!positional) die('module search needs query words, e.g. `--scope module "weak overlap rate"`.');
  const KINDS = new Set(["theorem", "def", "lemma", "structure", "inductive", "instance", "abbrev"]);
  const isAuto = (n: string): boolean =>
    /\.(congr_simp|congr|noConfusion|rec|recAux|casesOn|below|brecOn|sizeOf|eq_def|ext_iff)$|\.inst(DecidableEq|Repr)/.test(n);
  const declCount: Record<string, number> = {};
  const overviewOf: Record<string, string | null> = {};
  for (const l of r.libraries) {
    Object.assign(overviewOf, l.library.modules);
    for (const e of l.library.entries) {
      if (!KINDS.has(e.kind) || isAuto(e.name)) continue;
      declCount[e.module] = (declCount[e.module] ?? 0) + 1;
    }
  }
  const channels = semanticChannels(positional, useSemantic);
  const semantic: SearchOpts["semantic"] = channels.size > 0 ? { channels, fusion } : undefined;
  const libOf = new Map<string, string>();
  const cands = r.search({ mode: "concept", title: positional }, { topK: 80, semantic });
  for (const c of cands) libOf.set(c.module, c.library);
  const mods = poolModules(cands.map((c) => ({ module: c.module, name: c.name, score: c.score })), k, 3);
  const short = (n: string): string => n.split(".").slice(-1)[0];
  console.log(header(scopeArg, `${semantic ? " · +semantic" : ""} · top-3 pooled`, mods.length));
  console.log(scopeLine);
  for (const m of mods) {
    const overview = String(overviewOf[m.module] ?? "").split(/\n\s*\n/)[0].replace(/^#+\s*/, "").replace(/\s+/g, " ").trim();
    console.log(`\n  [${m.score.toFixed(3)}] ${m.module}   [${libOf.get(m.module) ?? "?"}] (${m.memberCount} matched · ${declCount[m.module] ?? "?"} decls)`);
    if (overview) console.log(`      ${overview.slice(0, 200)}`);
    if (m.prototypes.length) console.log(`      e.g. ${m.prototypes.map(short).join(", ")}`);
  }
  if (!mods.length) console.log("\n  (no matches)");
  process.exit(0);
}

let q: Query;
if (typePattern !== undefined) q = { mode: "typePattern", pattern: typePattern };
else if (goal !== undefined) q = { mode: "goal", goalType: goal };
else if (positional) q = { mode: "concept", title: positional };
else {
  die('usage: search [--index <path>... | --toolkit <path>] [<concept words> | --type "<pat>" | --goal "<type>" | --scope module "<words>"] [--k N] [--semantic] [--fusion rrf|weighted]');
}

let semantic: SearchOpts["semantic"];
if (q!.mode === "goal" || (useSemantic && q!.mode === "concept")) {
  const channels = semanticChannels(q!.mode === "goal" ? q!.goalType : positional, useSemantic);
  if (channels.size > 0) semantic = { channels, fusion };
} else if (useSemantic) {
  console.error("--semantic applies to concept and goal modes only; ignoring for --type.");
}
if (fusion && !semantic && q!.mode === "concept") console.error("--fusion only takes effect with a semantic tier active; ignoring.");

const hits = r.search(q!, { topK: k, semantic });
console.log(header(q!.mode, semantic ? ` · +semantic(${fusion ?? "rrf"})` : "", hits.length));
console.log(scopeLine);
for (const h of hits) {
  console.log(`\n  [${Number.isInteger(h.score) ? h.score : h.score.toFixed(3)}] ${h.name}   [${h.library}] (${h.matchedVia})`);
  console.log(`      ${h.statement.replace(/\s+/g, " ").slice(0, 140)}`);
  console.log(`      ${h.file}${h.tier1 ? " · tier-1" : ""}${h.usesSorry ? " · ⚠usesSorry" : ""}`);
  if (h.docFirstPara) console.log(`      ${h.docFirstPara.slice(0, 160)}`);
}
if (!hits.length) console.log("\n  (no matches)");
