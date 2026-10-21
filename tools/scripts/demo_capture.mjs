#!/usr/bin/env node
// The states behind `paperformalizer demo`: a dry run of the demo paper, its halts written in by hand
// (`tools/scripts/demo_author.mjs`), each state as the page shows it, kept so that the demo plays them
// back with no model call. Plain Node, no build step:
//
//   node tools/scripts/demo_capture.mjs copy --toolkit <path> --slug <slug> --to <raw dir>/<nnn>-<label>
//       Copy one state of the run as the page reads it (the run's directory less its logs, transcripts
//       and prompts; the toolkit's Lean trees and doc/), a dry run's shown as a live run's.
//   node tools/scripts/demo_capture.mjs build --raw <raw dir> --toolkit <path> --paper <dir>
//       --steps <name>=<nnn>,… --out <dir>
//       Write each chosen copy, in order, as an overlay on the one before (`<out>/<name>/files/…`, and
//       `<out>/<name>/removed.json`), the toolkit's path written @@TOOLKIT@@ and the paper's @@PAPER@@
//       (`src/demo/driver.ts` `applySnapshot` lays them down).
import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import path from "node:path";

const [cmd, ...args] = process.argv.slice(2);
const opt = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
const usage = "usage: demo_capture.mjs copy --toolkit <path> --slug <slug> --to <dir> | build --raw <raw dir> --toolkit <path> --paper <dir> --steps <name>=<nnn>,… --out <dir>";

/** What of a run the page reads, relative to the toolkit; `skip` drops a path under them. */
const TREES = (slug) => [`runs/${slug}`, "Toolkit", "Toolkit.lean", "Papers", "Papers.lean", "doc"];
const skip = (rel) => /(^|\/)(logs|codex_raw|prompts|dry_run_prompts|_archive|\.lake|voided)(\/|$)|\.(log|aux|out|fls|fdb_latexmk|synctex\.gz|lock)$/.test(rel) || /(^|\/)orch(_requests)?\.json$|(^|\/)start_request\.json$|(^|\/)\.run\.active/.test(rel);

function walk(root, rel, out) {
  const abs = path.join(root, rel);
  let st;
  try { st = statSync(abs); } catch { return out; }
  if (st.isDirectory()) { for (const e of readdirSync(abs)) { const r = rel ? `${rel}/${e}` : e; if (!skip(r)) walk(root, r, out); } }
  else if (st.isFile() && !skip(rel)) out.push(rel);
  return out;
}
const filesOf = (root, slug) => TREES(slug).flatMap((t) => walk(root, t, []));

if (cmd === "copy") {
  const toolkit = path.resolve(opt("--toolkit") ?? ""), slug = opt("--slug"), to = path.resolve(opt("--to") ?? "");
  if (!opt("--toolkit") || !slug || !opt("--to")) { console.error(usage); process.exit(64); }
  for (const f of filesOf(toolkit, slug)) { mkdirSync(path.dirname(path.join(to, f)), { recursive: true }); cpSync(path.join(toolkit, f), path.join(to, f)); }
  // a dry run's state shown as a live one's: its checklists where the page keeps a round's decisions
  // (doc/proposals/), and no dry-run mark
  const dry = path.join(to, "runs", slug, "proposals", "dry_run");
  for (const r of ["A", "B"]) {
    const md = path.join(dry, `${slug}.${r}.md`);
    if (!existsSync(md)) continue;
    mkdirSync(path.join(to, "doc", "proposals"), { recursive: true });
    cpSync(md, path.join(to, "doc", "proposals", `${slug}.${r}.md`));
  }
  rmSync(dry, { recursive: true, force: true });
  const stateFile = path.join(to, "runs", slug, "state.json");
  const state = JSON.parse(readFileSync(stateFile, "utf8"));
  delete state.verify.dry_run;
  writeFileSync(stateFile, JSON.stringify(state, null, 2).split(path.join(toolkit, "runs", slug, "proposals", "dry_run")).join(path.join(toolkit, "doc", "proposals")) + "\n");
  console.log(`[copy] ${to}`);
} else if (cmd === "build") {
  const raw = path.resolve(opt("--raw") ?? ""), out = path.resolve(opt("--out") ?? ""), tk = opt("--toolkit"), paper = opt("--paper");
  const steps = (opt("--steps") ?? "").split(",").filter(Boolean).map((s) => s.split("="));
  if (!opt("--raw") || !opt("--out") || !tk || !paper || !steps.length) { console.error(usage); process.exit(64); }
  const real = (p) => { try { return realpathSync(p); } catch { return path.resolve(p); } };
  // longest first, so that the paper's path inside the toolkit is not cut by the toolkit's
  const subs = [[real(paper), "@@PAPER@@"], [path.resolve(paper), "@@PAPER@@"], [real(tk), "@@TOOLKIT@@"], [path.resolve(tk), "@@TOOLKIT@@"]].sort((a, b) => b[0].length - a[0].length);
  const TEXT = /\.(json|jsonl|md|tex|lean|txt|toml|bib|csv|html)$/;
  const portable = (f) => { if (!TEXT.test(f)) return readFileSync(f); let t = readFileSync(f, "utf8"); for (const [from, to] of subs) t = t.split(from).join(to); return t; };
  if (existsSync(path.join(out, "demo.json")) || existsSync(path.join(out, "paper"))) { console.error(`${out} holds the demo's tour or paper: --out is the snapshots folder itself`); process.exit(64); }
  rmSync(out, { recursive: true, force: true });
  let prev = new Map(); // rel → sha of the portable text
  for (const [name, nnn] of steps) {
    const src = readdirSync(raw).find((d) => d.startsWith(`${nnn}-`));
    if (!src) { console.error(`no recorded state ${nnn} under ${raw}`); process.exit(65); }
    const root = path.join(raw, src);
    const now = new Map();
    let changed = 0;
    for (const rel of walk(root, "", [])) {
      const body = portable(path.join(root, rel));
      const sha = createHash("sha256").update(body).digest("hex");
      now.set(rel, sha);
      if (prev.get(rel) === sha) continue;
      const to = path.join(out, name, "files", rel);
      mkdirSync(path.dirname(to), { recursive: true });
      writeFileSync(to, body);
      changed++;
    }
    const removed = [...prev.keys()].filter((r) => !now.has(r));
    mkdirSync(path.join(out, name), { recursive: true });
    writeFileSync(path.join(out, name, "removed.json"), JSON.stringify(removed, null, 1) + "\n");
    console.log(`[build] ${name} ← ${src}: ${changed} file(s) written, ${removed.length} removed`);
    prev = now;
  }
} else { console.error(usage); process.exit(64); }
