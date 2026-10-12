import Lean.CoreM
import Lean.Replay

/-!
Replay the same import closure as the bundled `leanchecker --fresh QubitAdditivity`,
without its search-path-wide file enumeration. The replay body is the one in
Lean 4.34.1's LeanChecker.replayFromFresh. This uses Lean's own kernel and is not
an independently implemented external checker. It is not imported by the proofs.
-/

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  IO.println "Starting fresh kernel replay of QubitAdditivity and its imports."
  Lean.withImportModules #[{module := `QubitAdditivity}] {} fun env => do
    IO.println s!"Imported declarations to replay: {env.constants.map₁.size}"
    discard <| (← mkEmptyEnvironment).toKernelEnv.replay env.constants.map₁
  IO.println "Fresh kernel replay completed."
