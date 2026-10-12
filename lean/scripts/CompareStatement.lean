import Lean

/-!
Local statement comparison for a Comparator configuration such as
`ComparatorChallenges/QubitHolevoAdditivity.json`.

For every listed theorem this checks, in the two compiled environments, that

* the challenge and the solution declare it with the same universe parameters and type, and the
  solution's declaration is a theorem;
* every constant the statement depends on is either imported by both sides from the same
  compiled module, or is declared on both sides with the same kind, type and body;
* the solution's proof depends on no axiom outside the permitted list.

These are the checks of leanprover/comparator, run without its sandbox and without an export
to an external kernel. It is not that tool. Kernel replay is `scripts/Replay.lean`.
-/

open Lean

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  permitted_axioms : Array String
deriving FromJson

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

def sameRules : List RecursorRule → List RecursorRule → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    a.ctor == b.ctor && a.nfields == b.nfields && a.rhs == b.rhs && sameRules as bs
  | _, _ => false

/-- Same kind, universe parameters, type and body. Proofs of theorems are not compared. -/
def sameConst (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
  match a, b with
  | .defnInfo x, .defnInfo y => x.value == y.value && x.safety == y.safety
  | .thmInfo _, .thmInfo _ => true
  | .opaqueInfo x, .opaqueInfo y => x.value == y.value && x.isUnsafe == y.isUnsafe
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .quotInfo _, .quotInfo _ => true
  | .inductInfo x, .inductInfo y =>
    x.numParams == y.numParams && x.numIndices == y.numIndices && x.all == y.all &&
      x.ctors == y.ctors && x.isRec == y.isRec && x.isUnsafe == y.isUnsafe
  | .ctorInfo x, .ctorInfo y =>
    x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
      x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
    x.all == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.numMotives == y.numMotives && x.numMinors == y.numMinors && x.k == y.k &&
      x.isUnsafe == y.isUnsafe && sameRules x.rules y.rules
  | _, _ => false

/-- Compare the statement of `thm` and everything it depends on. Returns the constants that
are declared separately on the two sides and were compared. -/
def compareStatement (chal sol : Environment) (thm : Name) : IO (Array Name) := do
  let some c := chal.find? thm | throw <| IO.userError s!"challenge lacks {thm}"
  let some s := sol.find? thm | throw <| IO.userError s!"solution lacks {thm}"
  unless s matches .thmInfo _ do
    throw <| IO.userError s!"{thm} is not a theorem in the solution"
  unless c.levelParams == s.levelParams && c.type == s.type do
    throw <| IO.userError s!"{thm}: the two statements differ"
  let mut seen : NameSet := {}
  let mut todo : Array Name := c.type.getUsedConstants
  let mut compared : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some a := chal.find? n | throw <| IO.userError s!"challenge lacks {n}"
    let some b := sol.find? n | throw <| IO.userError s!"solution lacks {n}"
    match moduleOf chal n, moduleOf sol n with
    | some m₁, some m₂ =>
      -- A constant imported by both sides from one compiled module is literally the same.
      if m₁ == m₂ then continue
      unless sameConst a b do
        throw <| IO.userError s!"{n} is declared differently in {m₁} and {m₂}"
      compared := compared.push n
      for d in a.getUsedConstantsAsSet do
        todo := todo.push d
    | _, _ => throw <| IO.userError s!"{n} has no defining module"
  return compared

/-- Every axiom in the dependency cone of `thm`, proofs included. -/
def axiomsOf (env : Environment) (thm : Name) : IO (Array Name) := do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[thm]
  let mut found : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw <| IO.userError s!"unknown constant {n}"
    if ci matches .axiomInfo _ then found := found.push n
    for d in ci.getUsedConstantsAsSet do
      unless seen.contains d do todo := todo.push d
  return found

unsafe def main (args : List String) : IO UInt32 := do
  let path := args.headD "ComparatorChallenges/QubitHolevoAdditivity.json"
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cfg ← IO.ofExcept (fromJson? json : Except String Config)
  initSearchPath (← findSysroot)
  let chal ← importModules #[{module := cfg.challenge_module.toName}] {}
  let sol ← importModules #[{module := cfg.solution_module.toName}] {}
  IO.println s!"challenge: {cfg.challenge_module}"
  IO.println s!"solution: {cfg.solution_module}"
  for t in cfg.theorem_names do
    let thm := t.toName
    let compared ← compareStatement chal sol thm
    let axioms ← axiomsOf sol thm
    let extra := axioms.filter fun a => !cfg.permitted_axioms.contains a.toString
    unless extra.isEmpty do
      throw <| IO.userError s!"{thm} uses axioms outside the permitted list: {extra}"
    let names := compared.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{thm}: statement matches; {names.size} separately declared constants compared; axioms {axioms.qsort (fun a b => a.toString < b.toString)}"
    IO.println s!"  compared: {names}"
  IO.println "Local statement comparison passed."
  return 0
