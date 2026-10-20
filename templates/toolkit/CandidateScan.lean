import TheoremCheckerIndexCore

/-! # Candidate-scan exe (toolkit promotion and the toolkit graph)

Reports, for every declaration in its scope, the facts TheoremChecker's promotion round and
toolkit graph need: name, kind, pretty-printed type, docstring, module, source lines, the axioms it
depends on (`Lean.collectAxioms`, what `#print axioms` prints), whether it uses `sorry`, and every
constant its type and its body mention, each classified as

* `base`            — defined outside the toolkit and the papers library (Mathlib, Causalean, core …);
* `toolkit`         — defined in the toolkit library (staging excluded);
* `toolkit_staging` — defined in `<toolkit>.Staging.*` (never admitted);
* `paper`           — defined in the paper (`--paper`), or in any paper (`--graph`);
* `other_paper`     — defined in another paper's modules (`--paper` only);
* `unknown`         — no defining module (never expected in a loaded environment).

A constant of a reported declaration's own scope is reported by the name of the declaration it
belongs to (a constructor, projection, `match_`/`proof_` auxiliary or nested `where` helper
resolves to its owner; an owner-less auxiliary such as `_auxLemma` is expanded into the constants
it uses). The filters themselves are TypeScript; this exe only reports facts.

    lake exe candidate_scan -- --paper Papers.<Pascal> --out <json> [--modules M1,M2,…]
    lake exe candidate_scan -- --graph --out <json> [--modules Toolkit,Papers] [--rename old=new,…]
      [--toolkit-prefix Toolkit] [--papers-prefix Papers] [--fingerprints]

`--paper` reports that paper's declarations (imports `--modules`, default the paper's barrel);
`--graph` reports every toolkit and paper declaration (imports `--modules`, default the toolkit
and papers roots). `--fingerprints` reports only each declaration's name, kind, place and hashes
(`stmt_hash`, `closure_hash`): what the promotion gate and the F4 review cache read. Run from the
toolkit root after the modules are built. -/

open Lean

/-- The user-facing name of a (possibly private) declaration. -/
def userNameOf (n : Name) : Name := (privateToUserName? n).getD n

/-- Whether `n` is a declaration the scan reports on its own (not an auxiliary, constructor,
projection or compiler-generated companion). Mirrors the index extractor's filters, applied to
the user-facing name so private declarations are reported too. -/
def isReportedDecl (env : Environment) (mods : ModuleNames) (n : Name) : CoreM Bool := do
  let u := userNameOf n
  if isAuxiliary u || env.isConstructor n || env.isProjectionFn n || env.isConstructor n.getPrefix then
    return false
  if isSyntheticCompanionLeaf (declarationLeaf u) && (← findDeclarationRanges? n).isNone then
    return false
  let some ci := env.find? n | return false
  let some _ ← kindOf env n ci | return false
  -- A nested definition (`where` / `let rec` helper) whose range lies inside its parent's belongs
  -- to the parent.
  if let some parent := env.find? n.getPrefix then
    if parent.isDefinition || parent.isTheorem then
      if let some child ← findDeclarationRanges? n then
        if moduleNameOf? mods env n == moduleNameOf? mods env n.getPrefix then
          if let some p ← findDeclarationRanges? n.getPrefix then
            if !Position.lt child.range.pos p.range.pos && !Position.lt p.range.endPos child.range.endPos then
              return false
      else
        return false
  return true

structure ScanCtx where
  /-- Module prefix of the `paper` class: one paper (`--paper`) or the papers library (`--graph`). -/
  paper : Name
  toolkit : Name
  papers : Name
  /-- Module prefixes whose declarations are reported (and resolved to their owners). -/
  scope : Array Name
  /-- The reported declarations (internal names). -/
  reported : NameSet
  /-- Module names by module index, computed once (`ModuleNames`). -/
  mods : ModuleNames

def ScanCtx.inScope (c : ScanCtx) (m : Name) : Bool :=
  c.scope.any (·.isPrefixOf m) && !(c.toolkit ++ `Staging).isPrefixOf m

/-- The module class of a constant (see the module docstring). -/
def classOf (env : Environment) (c : ScanCtx) (n : Name) : String × String :=
  match moduleNameOf? c.mods env n with
  | none => ("unknown", "")
  | some m =>
    if c.paper.isPrefixOf m then ("paper", m.toString)
    else if (c.toolkit ++ `Staging).isPrefixOf m then ("toolkit_staging", m.toString)
    else if c.toolkit.isPrefixOf m then ("toolkit", m.toString)
    else if c.papers.isPrefixOf m then ("other_paper", m.toString)
    else ("base", m.toString)

/-- The reported declaration a constant of the scan's scope belongs to, if any. -/
partial def ownerOf (env : Environment) (c : ScanCtx) (n : Name) : Option Name :=
  if c.reported.contains n then some n
  else match env.find? n with
    | some (.ctorInfo v) => ownerOf env c v.induct
    | _ =>
      match env.getProjectionFnInfo? n with
      | some info =>
        match env.find? info.ctorName with
        | some (.ctorInfo v) => ownerOf env c v.induct
        | _ => walk n.getPrefix
      | none => walk n.getPrefix
where
  walk : Name → Option Name
    | .anonymous => none
    | p => if c.reported.contains p then some p else walk p.getPrefix

/-- Constants an expression-bearing constant mentions: type, value, and constructor types. -/
def constsOfInfo (env : Environment) (ci : ConstantInfo) : Array Name × Array Name :=
  let ctorTypes := match ci with
    | .inductInfo v => v.ctors.toArray.foldl (fun acc k =>
        match env.find? k with
        | some kci => acc ++ kci.type.getUsedConstants
        | none => acc) #[]
    | _ => #[]
  let body := match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  (ci.type.getUsedConstants ++ ctorTypes, body)

/-- Classified references of `self`: `(name, class, module)` triples, deduplicated. Constants of
the scan's scope are reported by owner (self-references dropped); owner-less auxiliaries are
expanded into what they use. -/
partial def classify (env : Environment) (c : ScanCtx) (self : Name) (names : Array Name) :
    Array (String × String × String) := Id.run do
  let mut out : Array (String × String × String) := #[]
  let mut seen : NameSet := {}
  let mut todo := names.toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let (cls, m) := classOf env c n
      if c.inScope m.toName then
        match ownerOf env c n with
        | some o =>
          if o != self then
            let key := (toString (userNameOf o), cls, m)
            if !out.contains key then out := out.push key
        | none =>
          -- An owner-less auxiliary (`_auxLemma.N`, a module-level `proof_N`): its content counts.
          match env.find? n with
          | some ci =>
            let (t, b) := constsOfInfo env ci
            todo := todo ++ (t ++ b).toList
          | none => pure ()
      else
        let key := (toString (userNameOf n), cls, m)
        if !out.contains key then out := out.push key
  return out.qsort (fun a b => a.1 < b.1)

def refsJson (xs : Array (String × String × String)) : Json :=
  Json.arr <| xs.map fun (n, cls, m) =>
    Json.mkObj [("name", Json.str n), ("class", Json.str cls), ("module", Json.str m)]

def ppType (ci : ConstantInfo) : CoreM String := do
  let fmt ← Meta.MetaM.run' <|
    withOptions
      (fun opts => opts |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (200000 : Nat))
      (Meta.ppExpr ci.type)
  return fmt.pretty (width := stmtPPWidth)

/-- `n` with the first matching prefix of `pairs` replaced (`old → new`): the name a declaration
(or one of its auxiliaries) takes once a promotion has moved it. -/
def renameName (pairs : Array (Name × Name)) (n : Name) : Name :=
  match pairs.find? (fun p => p.1.isPrefixOf n) with
  | some (o, t) => n.replacePrefix o t
  | none => n

/-- A structural hash of `e` that does not depend on what its universe parameters are called and
reads every constant under `pairs`. -/
def exprFingerprint (pairs : Array (Name × Name)) (lparams : List Name) (e : Expr) : UInt64 :=
  let canon := (List.range lparams.length).map fun i => Level.param (Name.mkNum `u i)
  let e := e.instantiateLevelParams lparams canon
  let e := if pairs.isEmpty then e else e.replace fun
    | .const k ls => some (.const (renameName pairs k) ls)
    | _ => none
  e.hash

/-- What a declaration STATES, as a hash: a theorem's type; a definition's type and value; a
structure's or inductive's type and constructor types. Two scans agree on it exactly when the
declaration says the same thing — whatever it is called (`--rename`) and however it is proved. A
promotion's gate compares it before and after a move. -/
def stmtFingerprint (env : Environment) (pairs : Array (Name × Name)) (ci : ConstantInfo) : UInt64 :=
  let h := exprFingerprint pairs ci.levelParams
  match ci with
  | .thmInfo _ => h ci.type
  | .inductInfo v => v.ctors.foldl (fun acc k =>
      match env.find? k with
      | some kci => mixHash acc (exprFingerprint pairs kci.levelParams kci.type)
      | none => acc) (h ci.type)
  | _ => match ci.value? (allowOpaque := true) with
    | some v => mixHash (h ci.type) (h v)
    | none => h ci.type

/-- Whether `n` is defined in the toolkit package — the toolkit library (staging included) or a
paper — rather than in a library the package depends on. -/
def ScanCtx.isLocal (c : ScanCtx) (env : Environment) (n : Name) : Bool :=
  match moduleNameOf? c.mods env n with
  | some m => c.toolkit.isPrefixOf m || c.papers.isPrefixOf m
  | none => false

/-- The constant whose statement stands for `n`: a constructor or recursor stands for its
inductive type; every other constant, compiler-generated ones included, for itself. -/
def stmtOwner (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.getMajorInduct
  | _ => n

/-- What `ci` states and nothing its statement leaves open: `stmtFingerprint`, with the names a
structural hash does not see — an inductive's constructors and a structure's fields. -/
def ownFingerprint (env : Environment) (ci : ConstantInfo) : UInt64 :=
  let h := stmtFingerprint env #[] ci
  match ci with
  | .inductInfo v =>
    let h := v.ctors.foldl (fun acc k => mixHash acc (hash k)) h
    if isStructure env ci.name then (getStructureFields env ci.name).foldl (fun acc f => mixHash acc (hash f)) h else h
  | _ => h

structure ClosureCache where
  /-- Per constant: the package constants its statement names (`stmtOwner`s, itself excluded). -/
  deps : Std.HashMap Name (Array Name) := {}

/-- The package constants the statement of `n` names directly: a theorem's type (never its
proof); a definition's type and value; an inductive's type and constructor types. -/
def stmtDeps (env : Environment) (c : ScanCtx) (n : Name) : StateM ClosureCache (Array Name) := do
  if let some d := (← get).deps[n]? then return d
  let used := match env.find? n with
    | some ci@(.thmInfo _) => ci.type.getUsedConstants
    | some ci => let (t, b) := constsOfInfo env ci; t ++ b
    | none => #[]
  let (d, _) := used.foldl (init := ((#[] : Array Name), ({} : NameSet))) fun (acc, seen) k =>
    let o := stmtOwner env k
    if o == n || seen.contains o || !c.isLocal env o then (acc, seen) else (acc.push o, seen.insert o)
  modify fun s => { s with deps := s.deps.insert n d }
  return d

/-- What `n` states together with everything of the package its statement rests on, as a hash:
`ownFingerprint` of `n` and of every package constant reachable from it through `stmtDeps`, each
under its name, in name order. It moves exactly when one of those statements does — not with a
proof, a comment, an option, or a declaration `n` does not reach. Library constants are read by
name (the pin fixes them). Compiler-generated constants (matchers, `_proof_` theorems, projections,
instances) are followed like any other. Not read under `--rename`. Returned with the number of
constants it covers. -/
def closureFingerprint (env : Environment) (c : ScanCtx) (n : Name) : StateM ClosureCache (UInt64 × Nat) := do
  let mut seen : NameSet := ({} : NameSet).insert n
  let mut todo := #[n]
  while !todo.isEmpty do
    let cur := todo.back!
    todo := todo.pop
    for d in ← stmtDeps env c cur do
      if !seen.contains d then
        seen := seen.insert d
        todo := todo.push d
  let members := seen.toArray.qsort Name.lt
  let h := members.foldl (init := 7) fun acc m =>
    match env.find? m with
    | some ci => mixHash acc (mixHash (hash m) (ownFingerprint env ci))
    | none => mixHash acc (hash m)
  return (h, members.size)

def scanDecl (env : Environment) (c : ScanCtx) (pairs : Array (Name × Name)) (closure : UInt64 × Nat) (hashesOnly : Bool) (n : Name) : CoreM (Option Json) := do
  let some ci := env.find? n | return none
  let some kind ← kindOf env n ci | return none
  let some m := moduleNameOf? c.mods env n | return none
  if hashesOnly then
    return some <| Json.mkObj [
      ("name", Json.str (toString (userNameOf n))),
      ("kind", Json.str kind),
      ("module", Json.str m.toString),
      ("file", Json.str (moduleToFile m)),
      ("stmt_hash", Json.str (toString (stmtFingerprint env pairs ci))),
      ("closure_hash", Json.str (toString closure.1)),
      ("closure_size", toJson closure.2)
    ]
  let (typeNames, bodyNames) := constsOfInfo env ci
  let axioms ← collectAxioms n
  let ranges ← findDeclarationRanges? n
  let line := ranges.map (·.range.pos.line) |>.getD 0
  let endLine := ranges.map (·.range.endPos.line) |>.getD 0
  let nameLine := ranges.map (·.selectionRange.pos.line) |>.getD 0
  let doc ← findDocString? env n
  let type ← ppType ci
  return some <| Json.mkObj [
    ("name", Json.str (toString (userNameOf n))),
    ("kind", Json.str kind),
    ("module", Json.str m.toString),
    ("file", Json.str (moduleToFile m)),
    ("line", toJson line),
    ("name_line", toJson nameLine),
    ("end_line", toJson endLine),
    ("is_private", toJson (isPrivateName n)),
    ("type", Json.str type),
    ("stmt_hash", Json.str (toString (stmtFingerprint env pairs ci))),
    ("closure_hash", Json.str (toString closure.1)),
    ("closure_size", toJson closure.2),
    ("doc", match doc with | some d => Json.str d | none => Json.null),
    ("axioms", toJson (axioms.map toString)),
    ("has_sorry", toJson (axioms.contains ``sorryAx)),
    ("type_constants", refsJson (classify env c n typeNames)),
    ("body_constants", refsJson (classify env c n bodyNames))
  ]

unsafe def main (args : List String) : IO Unit := do
  let get (flag : String) : Option String := do
    let i ← args.idxOf? flag
    args[i + 1]?
  let usage := "usage: candidate_scan (--paper <Papers.Pascal> | --graph) --out <path> [--toolkit-prefix Toolkit] [--papers-prefix Papers] [--modules m1,m2,…] [--rename old1=new1,old2=new2,…] [--fingerprints]"
  let graph := args.contains "--graph"
  let hashesOnly := args.contains "--fingerprints"
  let some out := get "--out" | throw <| IO.userError usage
  let toolkit := (get "--toolkit-prefix").map (·.toName) |>.getD `Toolkit
  let paperStr ← match get "--paper", graph with
    | some p, false => pure p
    | none, true => pure ((get "--papers-prefix").getD "Papers")
    | _, _ => throw <| IO.userError usage
  let paper := paperStr.toName
  let papers := (get "--papers-prefix").map (·.toName) |>.getD (paper.getRoot)
  let scope : Array Name := if graph then #[toolkit, papers] else #[paper]
  let defaultMods := if graph then s!"{toolkit},{papers}" else paperStr
  let imports : Array Name :=
    ((get "--modules").getD defaultMods).splitOn ","
      |>.filterMap (fun s =>
          let t := s.trimAscii.toString
          if t.isEmpty then none else some t.toName)
      |>.toArray
  -- `--rename`: read each constant under these prefixes' new names when hashing statements.
  let pairs : Array (Name × Name) :=
    ((get "--rename").getD "").splitOn ","
      |>.filterMap (fun s =>
          match s.splitOn "=" with
          | [o, t] =>
            let o := o.trimAscii.toString
            let t := t.trimAscii.toString
            if o.isEmpty || t.isEmpty then none else some (o.toName, t.toName)
          | _ => none)
      |>.toArray
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (imports.map fun m => { module := m : Import }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<candidate_scan>", fileMap := default, maxHeartbeats := 0 }
  let run : CoreM Json := do
    let env ← getEnv
    let modNames := env.header.moduleNames
    let inScope (m : Name) := scope.any (·.isPrefixOf m) && !(toolkit ++ `Staging).isPrefixOf m
    let mut reported : NameSet := {}
    for (n, _) in env.constants.toList do
      if let some m := moduleNameOf? modNames env n then
        if inScope m && (← isReportedDecl env modNames n) then
          reported := reported.insert n
    let c : ScanCtx := { paper, toolkit, papers, scope, reported, mods := modNames }
    let mut decls : Array Json := #[]
    let mut cache : ClosureCache := {}
    for n in reported.toArray.qsort (fun a b => (userNameOf a).toString < (userNameOf b).toString) do
      let (closure, cache') := (closureFingerprint env c n).run cache
      cache := cache'
      if let some j ← scanDecl env c pairs closure hashesOnly n then decls := decls.push j
    let modules := modNames.filter inScope |>.map (·.toString)
    return Json.mkObj [
      ("schema", toJson (1 : Nat)),
      ("paper", Json.str paper.toString),
      ("graph", toJson graph),
      ("toolkit_prefix", Json.str toolkit.toString),
      ("papers_prefix", Json.str papers.toString),
      ("toolchain", Json.str s!"leanprover/lean4:v{Lean.versionString}"),
      ("modules", toJson modules),
      ("declarations", Json.arr decls)
    ]
  let (json, _) ← run.toIO ctx { env }
  if let some parent := (System.FilePath.mk out).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile out (json.pretty ++ "\n")
  let n := match json.getObjValD "declarations" with | .arr a => a.size | _ => 0
  IO.println s!"candidate_scan: {n} declarations -> {out}"
