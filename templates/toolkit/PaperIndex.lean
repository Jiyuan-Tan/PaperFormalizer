import TheoremCheckerIndexCore

/-! # Paper-module index exe

Indexes the Lean modules of one verified paper into a `library_index.json`-shaped file, with
the toolkit's index extractor (`TheoremCheckerIndexCore.runIndex`, a copy of Causalean's).
TheoremChecker's F5 docstring-coverage gate calls it as

    lake -d <toolkit> exe paper_index -- --prefix Papers.<Pascal> --src-root <toolkit>
      --modules Papers.<Pascal>,Papers.<Pascal>.A,… --out <run>/formalization/docstring_coverage.json

`--prefix` selects the declarations (every module under it); `--modules` are imported directly,
so the index does not depend on the paper being reachable from the `Papers` root barrel (an
in-progress paper joins it only when its F5 completes); `--src-root` is the directory the
`<Module/Path>.lean` source files resolve against. Defaults: prefix `Papers`, source root `.`.
Run from the toolkit root (it records that directory's git commit). Declarations of modules
unchanged since the paper's previous run are reused from a machine-local cache under
`.lake/build/paper_index/`, one file per prefix; set `LIBRARY_INDEX_FULL` to rederive everything. -/

unsafe def main (args : List String) : IO Unit := do
  let get (flag : String) : Option String := do
    let i ← args.idxOf? flag
    args[i + 1]?
  let pfx := (get "--prefix").map (·.toName) |>.getD `Papers
  let some out := get "--out"
    | throw <| IO.userError "usage: paper_index --out <path> [--prefix <module-prefix>] [--src-root <dir>] [--modules m1,m2,…]"
  let srcRoot := (get "--src-root").getD "."
  let extra : Array Lean.Name :=
    ((get "--modules").getD "").splitOn ","
      |>.filterMap (fun s =>
          let t := s.trimAscii.toString
          if t.isEmpty then none else some t.toName)
      |>.toArray
  runIndex `Papers pfx srcRoot out extra (cachePath := some s!".lake/build/paper_index/{pfx}.json")
