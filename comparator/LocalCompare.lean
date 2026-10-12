/- Local preflight only: compare separately elaborated environments using the pinned
Comparator's declaration-equality rules. No Linux sandbox or kernel replay is claimed. -/
/- Traversal adapted from leanprover/comparator, ca04cfc72b550331658ec314bf47685281bfd4bf.
Copyright (c) 2025 Lean FRO, LLC. Released under Apache 2.0. -/
import Lean

open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def primitiveNames : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce,
  ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam,
  ``semiOutParam, ``outParam]

def dependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut result := info.type.getUsedConstants ++
    (info.value? (allowOpaque := true) |>.map (·.getUsedConstants)).getD #[]
  match info with
  | .inductInfo i => result := result ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => result := result.push i.induct
  | .recInfo i =>
    for rule in i.rules do
      result := result.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return result

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{module := `ComparatorChallenges.QubitHolevoAdditivity}] {}
  let solution ← importModules #[{module := `QubitAdditivity.FCPresentation}] {}
  let targets := #[`QubitHolevo.strong_additivity, `QubitHolevo.power_additivity]
  let legal := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in targets do
    let some c := challenge.find? target | throw <| IO.userError s!"No challenge theorem {target}"
    let some s := solution.find? target | throw <| IO.userError s!"No solution theorem {target}"
    unless c matches .thmInfo _ do throw <| IO.userError "Challenge target is not a theorem"
    unless s matches .thmInfo _ do throw <| IO.userError "Solution target is not a theorem"
    unless c.toConstantVal == s.toConstantVal do
      throw <| IO.userError s!"Target statement differs: {target}"
    let mut seen : NameSet := {}
    let mut todo := c.type.getUsedConstants ++ primitiveNames ++ legal
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some a := challenge.find? n | throw <| IO.userError s!"Missing challenge declaration {n}"
      let some b := solution.find? n | throw <| IO.userError s!"Missing solution declaration {n}"
      unless a == b do throw <| IO.userError s!"Declaration differs: {n}"
      todo := todo ++ dependencies a
    IO.println s!"LOCAL_MATCH target={target} declaration_count={seen.size} mismatches=0"
  for theoremName in targets.push `QubitAdditivity.GeneralResult.generalQubitStrongAdditivity do
    let mut checked : NameSet := {}
    let mut work := #[theoremName]
    let mut axioms : NameSet := {}
    while !work.isEmpty do
      let n := work.back!
      work := work.pop
      if checked.contains n then continue
      checked := checked.insert n
      let some info := solution.find? n | throw <| IO.userError s!"Missing proof constant {n}"
      if info matches .axiomInfo _ then
        unless legal.contains n do throw <| IO.userError s!"Illegal axiom {n}"
        axioms := axioms.insert n
      work := work ++ dependencies info
    unless legal.all axioms.contains do throw <| IO.userError "Axiom set differs from recorded expectation"
    IO.println s!"'{theoremName}' depends on axioms: [propext, Classical.choice, Quot.sound]"
  IO.println "LOCAL_SCOPE declaration equality only; Linux sandbox and kernel replay NOT_RUN"
  -- Both large imported environments are finished; let the process reclaim them.
  (← IO.getStdout).flush
  IO.Process.exit 0
