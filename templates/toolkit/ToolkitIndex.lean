import LeanSmithIndexCore

/-! # Toolkit-index exe

Walks the elaborated environment of `import Toolkit` and writes `doc/toolkit_index.json`, one
record per `Toolkit.*` declaration, in the same JSON shape as Causalean's
`doc/library_index.json` (`LeanSmithIndexCore.runIndex`, a copy of its extractor). LeanSmith's
retrieval reads it as the toolkit's index source, and `npm run search -- --index` accepts it.
Run `lake exe toolkit_index` from the toolkit root after `lake build Toolkit`.

Optional flags: `--lib <name>` (the toolkit library, default `Toolkit`), `--out <path>`
(default `doc/toolkit_index.json`), `--src-root <dir>` (default `.`). Declarations of modules
unchanged since the previous run are reused from a machine-local cache under `.lake/build/`; set
`LIBRARY_INDEX_FULL` to rederive everything. -/

unsafe def main (args : List String) : IO Unit := do
  let get (flag : String) : Option String := do
    let i ← args.idxOf? flag
    args[i + 1]?
  let lib := (get "--lib").map (·.toName) |>.getD `Toolkit
  let out := (get "--out").getD "doc/toolkit_index.json"
  let srcRoot := (get "--src-root").getD "."
  runIndex lib lib srcRoot out (cachePath := some s!".lake/build/{lib}_index_cache.json")
