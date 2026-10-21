# Porting a library to PaperFormalizer's pin

Every optional library PaperFormalizer offers builds against one Lean toolchain and one Mathlib
revision, the pin in `tools/data/libraries.json`. A library whose upstream is on another pin is
offered as an **adapted copy** under `third_party/<Name>/`. A library is only usable from a
toolkit when it is also a **module library** (step 3). This is how a copy is made (FoML, optlib
and StatLean were made this way). A port is hours of work for a small library and much more for a
large one: agree it with the user before starting.

## 1. Workspace

Work in a scratch directory outside the repository:

    git clone https://github.com/<owner>/<repo> upstream          # note the commit: git -C upstream rev-parse HEAD
    mkdir port && cp -r upstream/<Lib> upstream/<Lib>.lean port/
    cd port
    echo "<lean_toolchain from libraries.json>" > lean-toolchain

and a `lakefile.toml` with the library and Mathlib at the pin (the upstream's other requires, if any,
before mathlib, each at a revision that itself builds against the pin):

    name = "<Lib>"
    defaultTargets = ["<Lib>"]

    [[require]]
    name = "mathlib"
    scope = "leanprover-community"
    rev = "<mathlib_rev from libraries.json>"

    [[lean_lib]]
    name = "<Lib>"

Then `lake exe cache get` (Mathlib's prebuilt oleans) and `lake build > build.log 2>&1`. The log
lists every failing module; count `^error:` lines to measure the gap before committing to a port.

## 2. Fix the build

Rules — the copy must state exactly what upstream states:

- No statement changes meaning. Do not weaken, delete or reformulate a theorem or a definition;
  spelling a statement with Mathlib's new name for the same notion is fine.
- No `sorry`, `admit`, `axiom`, or option that switches checking off. Count upstream's own first
  (`grep -rnE "\bsorry\b|\badmit\b|^\s*axiom\b" <Lib>`) and add none.
- Minimal local fixes: renamed lemmas (find the new name in `.lake/packages/mathlib`, or with
  `#check` / `exact?` under `lake env lean`), changed simp normal forms, explicit coercions, adjusted
  tactic calls.
- Leaves first: fix the modules others import, rebuild, repeat. New errors surface in modules that
  were blocked behind a failure; the count can rise before it falls.
- Anything that cannot be ported without changing its meaning is left out of the copy and listed
  in `UPSTREAM.md` — never weakened to fit.

Done when `lake build` completes with no errors and the `sorry`/`axiom` count equals upstream's.

## 3. Convert it to the Lean module system

Why: every file of a toolkit (`Toolkit/`, `Papers/`) starts with `module`, and Lean refuses a
plain library there — `error: cannot import non-`module` <Lib>.X from `module``. A library that
only builds on the pin is therefore still unusable. (A library whose upstream already is a module
library skips to the check.)

Procedure, as FoML and optlib were converted — in every `.lean` file of the library, the root
`<Lib>.lean` included:

1. Put `module` on its own line before the first `import` (after the copyright comment, if any).
2. Turn every `import X` into `public import X`.
3. Put `@[expose] public section` on its own line after the imports and the module docstring
   (`/-! … -/`), before the first `open`, `namespace`, `variable` or declaration. It is never
   closed: it runs to the end of the file. Everything below it stays as it is — `namespace`,
   `open`, `section … end`, `noncomputable section`, `variable`, `private` declarations, `local`
   notation and instances.
4. In the lakefile, set `requiresModuleSystem = true` on the library (`requiresModuleSystem :=
   true` in a `lakefile.lean`).

Then rebuild and fix what the new visibility rules break, under the rules of step 2 (no statement
changes, no `sorry`). In the two ports this was rare: a `private` helper that a proof in another
file needs loses its `private`, and a proof that relied on unfolding something no longer visible
gets an explicit step. The blanket `@[expose] public section` is what keeps such repairs few: it
exports every definition's body, as before the conversion. A file that defines syntax, macros,
tactics or other compile-time code needs more than this (`meta` imports and sections; see the Lean
reference on modules); neither port had one.

Check, both parts:

- `lake build` of the copy completes, and `tools/bin/lint_module_headers.ts --strict --paths
  <Lib> <Lib>.lean` (from `tools/`, `npx tsx …`) reports no error (its warning that `@[expose]` has
  no effect in a theorem-only file is expected with the blanket section).
- A probe builds: in a scratch toolkit that requires the library together with every other
  library on offer (`paperformalizer init <scratch> --libraries <the others>`, then add the new
  `[[require]]` by hand, before mathlib), a file

      module

      public import Mathlib
      public import <Lib>
      public import <each other installed library's root>

  compiles with `lake env lean Probe.lean` (after `lake build` of each library named). This is
  what a paper's Lean will do. It also catches a declaration that two libraries both define (the
  import fails: the environment already contains the name), which no single library's build shows. Resolve a clash by **renaming the declaration in the copy** (and its
  uses there), never by deleting it or weakening either statement, and record the old and new
  name in `UPSTREAM.md`. Never rename in Mathlib or in a git-required library.

Record in `UPSTREAM.md`: that and when the copy was converted and how (blanket `@[expose] public
section`), each repair the conversion needed, each renamed declaration, and that upstream diffs
are to be re-applied on top of the module header, not in place of it.

## 4. Vendor it

    third_party/<Name>/
      <Lib>/, <Lib>.lean        the ported sources
      lakefile.lean | .toml     the library, Mathlib at the pin
      lean-toolchain
      LICENSE (and LICENSES/)   upstream's, unchanged
      UPSTREAM.md

`UPSTREAM.md` records: the origin URL and the upstream commit ported; the license; why it is
vendored (upstream's pin vs ours); what was adapted (fix categories with counts, the module
conversion of step 3, and anything left out, with the reason); how to re-sync. The upstream
`LICENSE`, any `NOTICE`, and the authors' headers in the files stay as they are. No build output
(`.lake/`) goes in. Add the library to the README's "Acknowledgements".

## 5. Offer it

Add or update its entry in `tools/data/libraries.json` (`summary`, `require: {path:
"third_party/<Name>"}`, `lib`; remove `unavailable` if set) and the domains that should install
it. A copy that has not passed step 3 keeps `unavailable` (one line a user can read): `init`
then lists it as not yet available and no domain installs it. `npm test` checks the
copy is on the pin and a module library (`test/toolkit/init.test.ts`). Then check a real
install: `paperformalizer init <scratch-dir> --libraries <Name>` builds it and writes its index; a
`npx tsx bin/search.ts --toolkit <scratch-dir> "<a topic of the library>"` should find its results.
