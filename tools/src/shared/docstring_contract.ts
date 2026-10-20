// The docstring contract every Lean-writing stage states: F5 (a paper's modules) and the
// toolkit builders (study / promotion). One text, so a paper's docstrings and the toolkit's
// carry the same NL ↔ Lean crosslinks (see shared/nl_crosslinks.ts).
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const CONTRACT = readFileSync(
  path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts", "docstring_contract.txt"),
  "utf8",
).trim();

export function docstringContract(): string {
  return CONTRACT;
}
