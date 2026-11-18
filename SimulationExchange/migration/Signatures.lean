import Lean
import SimulationExchange
open Lean Elab Command Meta
/-- Print the fully explicit type of every non-internal declaration of a module. -/
elab "#signatures " m:ident : command => do
  let env ← getEnv
  let mut out : Array String := #[]
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    match env.getModuleIdxFor? name with
    | some idx =>
      if env.header.moduleNames[idx.toNat]! == m.getId then
        let s ← liftTermElabM do
          withOptions (fun o => o.setBool `pp.all true) do
            return toString (← ppExpr ci.type)
        out := out.push s!"{name} :: {s.replace "\n" " "}"
    | none => pure ()
  for l in out.qsort (· < ·) do logInfo m!"{l}"
#signatures SimulationExchange.Core
#signatures SimulationExchange.Model
#signatures SimulationExchange.Walkers
#signatures SimulationExchange.Meeting
#signatures SimulationExchange.Boundary
#signatures SimulationExchange.Instances
#signatures SimulationExchange.Switching
