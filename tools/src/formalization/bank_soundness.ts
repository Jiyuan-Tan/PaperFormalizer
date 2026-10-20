// F5 soundness gate: text-based (no LSP) scan of a run's Lean artifact subdir plus its
// reachable closure inside the same Lake project (the toolkit and paper libraries) for real
// `sorry` tokens and cheat tokens. Pure scanning — no Lean elaboration.

import { existsSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { listLeanFiles } from "../pipeline_support.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { LEAN_IMPORT_RE_GM, parseLeanImport } from "../shared/lean_syntax.js";

/** repoRoot-relative (forward-slash) form of a path. */
function relOf(file: string, repoRoot: string): string {
  const r = path.isAbsolute(file) ? path.relative(repoRoot, file) : file;
  return r.split(path.sep).join("/");
}

/** True when `root` is a library of the Lake project at `repoRoot`: a source directory or
 *  root module sits directly under it. Dependencies (Mathlib, base libraries) live elsewhere. */
function isProjectLibrary(root: string, repoRoot: string): boolean {
  const dir = path.join(repoRoot, root);
  try {
    if (statSync(dir).isDirectory()) return true;
  } catch {
    /* not a directory */
  }
  return existsSync(`${dir}.lean`);
}

/** Artifact files plus the transitive closure of every file they import from this Lake project
 *  (an import whose root component is a project library; its file is `<repoRoot>/<path>.lean`). */
function reachableFileClosure(researchFiles: string[], repoRoot: string): string[] {
  const seen = new Set<string>();
  const all: string[] = [];
  const queue = [...researchFiles];
  while (queue.length) {
    const f = queue.shift()!;
    const abs = path.isAbsolute(f) ? f : path.join(repoRoot, f);
    if (seen.has(abs)) continue;
    seen.add(abs);
    all.push(abs);
    let src: string;
    try {
      src = readFileSync(abs, "utf8");
    } catch {
      continue;
    }
    for (const m of maskLeanCommentsAndStrings(src).matchAll(LEAN_IMPORT_RE_GM)) {
      const imported = parseLeanImport(m[0]);
      if (!imported) continue;
      // A component written `«Foo Bar»` resolves to the file `Foo Bar.lean`: Lean's module path
      // uses the raw name, so the guillemets are escaping, not part of the path.
      const components = imported.module.split(".").map((c) => c.replace(/^«(.*)»$/u, "$1"));
      if (!isProjectLibrary(components[0], repoRoot)) continue;
      // A missing in-project file stays in the closure: the scan reports it unreadable (fail closed).
      queue.push(path.join(repoRoot, components.join("/") + ".lean"));
    }
  }
  return all;
}

/** The cheat tokens (axiom/opaque/unsafe/admit/sorry; admitted-proof tokens too, so closure
 *  banking cannot launder them as non-cheats). `native_decide` was removed from this list on
 *  2026-09-04 (operator call) — do not re-add; keep aligned with `scanResearchCheatTokens` in
 *  `proof_review_loop.ts`. */
const CHEAT_TOKEN = /\b(axiom|opaque|unsafe|admit|sorry|sorryAx)\b/;

/**
 * F5 soundness gate: scan the artifact subdir plus its reachable in-project
 * closure for real `sorry` tokens and cheat tokens. Returns human-readable issue
 * strings; empty = sound.
 */
export async function bankSoundnessIssues(leanDir: string, repoRoot: string): Promise<string[]> {
  const issues: string[] = [];
  for (const abs of reachableFileClosure(await listLeanFiles(leanDir), repoRoot)) {
    let text: string;
    try {
      text = readFileSync(abs, "utf8");
    } catch {
      issues.push(`unreadable file ${relOf(abs, repoRoot)}`);
      continue;
    }
    // Comments AND string literals are masked (newlines preserved, so line numbers stay
    // accurate): a docstring or a `"… sorry …"` message naming a token is not a token.
    const lines = maskLeanCommentsAndStrings(text).split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const m = CHEAT_TOKEN.exec(lines[i]);
      if (m) issues.push(`${m[1]} in ${relOf(abs, repoRoot)}:${i + 1}`);
    }
  }
  return issues;
}
