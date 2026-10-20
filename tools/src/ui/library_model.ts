// The toolkit library for the UI, read from the Lean sources themselves (always current; no index
// to refresh): modules with their `/-! -/` overview, declarations with their docstring and
// signature, "uses" links from the signatures, and which papers use each declaration (a full-name
// reference, or the bare name in a file that opens the declaration's namespace).
import { existsSync, readdirSync } from "node:fs";
import path from "node:path";
import type { ToolkitConfig } from "../toolkit/config.js";
import { readCached, signature } from "./fscache.js";

export interface LibDecl {
  name: string;
  leaf: string;
  kind: string;
  doc: string;
  sig: string;
  uses: string[];
  usedBy: string[];
  papers: string[];
  line: number;
}
export interface LibModule {
  path: string;
  module: string;
  title: string;
  summary: string;
  decls: LibDecl[];
}
export interface Library { modules: LibModule[]; papers: string[]; generic: number; linked: number }

/** The `.lean` files under `dir`; a directory named in `skip` is not entered. */
function walk(dir: string, skip: ReadonlySet<string> = new Set()): string[] {
  if (!existsSync(dir)) return [];
  const out: string[] = [];
  for (const d of readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, d.name);
    if (d.isDirectory()) { if (!skip.has(d.name)) out.push(...walk(p, skip)); }
    else if (d.name.endsWith(".lean")) out.push(p);
  }
  return out.sort();
}

const DECL_RE = /\/--((?:(?!-\/)[\s\S])*?)-\/\s*(?:--[^\n]*\n\s*)*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*(theorem|lemma|def|abbrev|structure|class|instance)\s+([^\s({[⦃:]+)([\s\S]*?)(?=:=|\n\s*where\b|\n\n|$)/g;

/** Module overview → { title, summary }: a `# Title` paragraph (a dotted module name does not count). */
function moduleDoc(text: string): { title: string; summary: string } {
  const m = /\/-!([\s\S]*?)-\//.exec(text);
  if (!m) return { title: "", summary: "" };
  const paras = m[1].trim().split(/\n\s*\n/).map((p) => p.replace(/\s+/g, " ").trim()).filter(Boolean);
  let title = "";
  if (paras[0]?.startsWith("#")) title = paras.shift()!.replace(/^#+\s*/, "");
  let summary = paras[0] ?? "";
  if (/^[A-Z][\w]*(\.[\w]+)+$/.test(title) && summary) { title = summary; summary = paras[1] ?? ""; }
  return { title, summary };
}

/** Declarations of one Lean file (docstring first paragraph, kind, name, signature). Pure. */
export function parseModule(raw: string): Array<Omit<LibDecl, "uses" | "usedBy" | "papers">> {
  const text = raw.replace(/\r\n?/g, "\n");
  const ns = /^namespace\s+(\S+)/m.exec(text)?.[1] ?? "";
  const out: Array<Omit<LibDecl, "uses" | "usedBy" | "papers">> = [];
  for (const m of text.matchAll(DECL_RE)) {
    const leaf = m[3].split(".").pop()!;
    out.push({
      name: ns && !m[3].startsWith(ns) ? `${ns}.${m[3]}` : m[3],
      leaf,
      kind: m[2] === "lemma" ? "theorem" : m[2],
      doc: m[1].trim().split(/\n\s*\n/)[0]!.replace(/\s+/g, " "),
      sig: m[4].replace(/\s+/g, " ").trim().slice(0, 2000),
      line: text.slice(0, m.index).split("\n").length,
    });
  }
  return out;
}

/** A Lean identifier (dotted), as far as a name reference needs it. */
const IDENT_RE = /[\p{L}_][\p{L}\p{N}_'!?.]*/gu;
/** The most segments a name is matched by (deeper than any declaration name; bounds a long `h.1.2.…`). */
const MAX_SEGS = 12;

/**
 * The names a paper's files can reach a declaration by, read once per paper: `full` holds every
 * dotted run of segments of every identifier (`A.B.c.mp` gives `A.B.c`, `B.c`, `c.mp`, …), and
 * `opened` maps each namespace a file opens (a dotted run on an `open` line) to the leading runs
 * (`A`, `A.B`, `A.B.c`, …) of the identifiers written in that file — not one written after a `.`,
 * which is a field or dot-notation on something else. One pass over the text; lookups per declaration.
 */
export interface PaperNames { full: Set<string>; opened: Map<string, Set<string>> }

function segments(token: string): string[] {
  return token.split(".").filter(Boolean).slice(0, MAX_SEGS);
}

export function paperNames(texts: string[]): PaperNames {
  const full = new Set<string>();
  const opened = new Map<string, Set<string>>();
  for (const t of texts) {
    const leading = new Set<string>();
    for (const m of t.matchAll(IDENT_RE)) {
      const segs = segments(m[0]);
      for (let i = 0; i < segs.length; i++) for (let j = i + 1; j <= segs.length; j++) full.add(segs.slice(i, j).join("."));
      if (t[m.index! - 1] === ".") continue;
      for (let j = 1; j <= segs.length; j++) leading.add(segs.slice(0, j).join("."));
    }
    for (const line of t.matchAll(/^\s*open\s+([^\n]*)/gm)) {
      for (const m of line[1]!.matchAll(IDENT_RE)) {
        const segs = segments(m[0]);
        for (let i = 0; i < segs.length; i++) for (let j = i + 1; j <= segs.length; j++) {
          const ns = segs.slice(i, j).join(".");
          const set = opened.get(ns) ?? new Set<string>();
          for (const h of leading) set.add(h);
          opened.set(ns, set);
        }
      }
    }
  }
  return { full, opened };
}

/**
 * Does the paper name the declaration `name` (fully qualified): the full name, or the rest of it
 * after a namespace prefix the file opens (`open A.B` then `c.d` or `B.c.d` for `A.B.c.d`).
 */
export function paperUses(names: PaperNames, name: string): boolean {
  if (names.full.has(name)) return true;
  const segs = name.split(".");
  for (let i = 1; i < segs.length; i++) {
    if (names.opened.get(segs.slice(0, i).join("."))?.has(segs.slice(i).join("."))) return true;
  }
  return false;
}

let cache: { key: string; lib: Library } | null = null;
const namesCache = new Map<string, { sig: string; names: PaperNames }>();
let building: { key: string; run: Promise<Library> } | null = null;

export async function readLibrary(cfg: ToolkitConfig): Promise<{ lib: Library; key: string }> {
  const libFiles = cfg.divisions.flatMap((d) => walk(path.join(cfg.toolkitRoot, cfg.lib, d)));
  const papersRoot = path.join(cfg.toolkitRoot, cfg.papersLib);
  // a run's scratch copies (`<Paper>/tmp/…`) are neither the paper's Lean nor a reason to recompute
  const paperFiles = walk(papersRoot, new Set(["tmp"])).filter((f) => path.relative(papersRoot, f).includes(path.sep));
  const key = [...libFiles, ...paperFiles].map((f) => `${f}:${signature(f)}`).join("|");
  if (cache && cache.key === key) return { lib: cache.lib, key: String(hash(key)) };
  // requests that arrive while the same library is being built share that build
  if (building?.key !== key) {
    const run = buildLibrary(cfg, libFiles, papersRoot, paperFiles).finally(() => { if (building?.run === run) building = null; });
    building = { key, run };
  }
  const lib = await building.run;
  cache = { key, lib };
  return { lib, key: String(hash(key)) };
}

async function buildLibrary(cfg: ToolkitConfig, libFiles: string[], papersRoot: string, paperFiles: string[]): Promise<Library> {
  const modules: LibModule[] = [];
  for (const f of libFiles) {
    const text = (await readCached(f)) ?? "";
    const rel = path.relative(path.join(cfg.toolkitRoot, cfg.lib), f).split(path.sep).join("/").replace(/\.lean$/, "");
    const decls = parseModule(text).map((d) => ({ ...d, uses: [] as string[], usedBy: [] as string[], papers: [] as string[] }));
    if (decls.length === 0) continue; // barrels
    modules.push({ path: rel, module: `${cfg.lib}.${rel.split("/").join(".")}`, ...moduleDoc(text), decls });
  }
  const byLeaf = new Map<string, LibDecl>();
  for (const m of modules) for (const d of m.decls) byLeaf.set(d.leaf, d);
  for (const m of modules) for (const d of m.decls) {
    const toks = new Set((d.sig.match(/[A-Za-z_][A-Za-z0-9_.']*/g) ?? []).map((t) => t.split(".").pop()!));
    d.uses = [...toks].filter((t) => t !== d.leaf && byLeaf.has(t)).sort();
    for (const u of d.uses) byLeaf.get(u)!.usedBy.push(d.leaf);
  }
  // paper usage, by paper directory; a paper's names are read again only when one of its files changed
  const files = new Map<string, string[]>();
  for (const f of paperFiles) {
    const paper = path.relative(papersRoot, f).split(path.sep)[0]!;
    files.set(paper, files.get(paper) ?? []);
    files.get(paper)!.push(f);
  }
  const papers = new Map<string, PaperNames>();
  for (const [paper, fs] of files) {
    const sig = fs.map((f) => `${f}:${signature(f)}`).join("|");
    let hit = namesCache.get(paper);
    if (hit?.sig !== sig) {
      hit = { sig, names: paperNames(await Promise.all(fs.map(async (f) => (await readCached(f)) ?? ""))) };
      namesCache.set(paper, hit);
    }
    papers.set(paper, hit.names);
  }
  for (const paper of namesCache.keys()) if (!files.has(paper)) namesCache.delete(paper);
  for (const m of modules) for (const d of m.decls) {
    for (const [paper, names] of papers) if (paperUses(names, d.name)) d.papers.push(paper);
  }
  const all = modules.flatMap((m) => m.decls);
  const lib: Library = {
    modules,
    papers: [...papers.keys()].sort(),
    generic: all.filter((d) => /^(Given|Under|For) \[the (stated|supplied)/.test(d.doc)).length,
    linked: all.filter((d) => /\]\((hyp:|goal)/.test(d.doc)).length,
  };
  return lib;
}

function hash(s: string): number {
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 16777619);
  return h >>> 0;
}
