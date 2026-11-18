import Lean
import SimulationExchange
open Lean Elab Command
elab "#audit_module " m:ident : command => do
  let env ← getEnv
  let mut clean : Array Name := #[]
  let mut dirty : Array String := #[]
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | some idx =>
      if env.header.moduleNames[idx.toNat]! == m.getId then
        let axs ← liftCoreM (Lean.collectAxioms name)
        if axs.isEmpty then clean := clean.push name
        else dirty := dirty.push s!"{name} {axs}"
    | none => pure ()
  logInfo m!"{m.getId}: {clean.size + dirty.size} declarations, {dirty.size} with axioms"
  for d in dirty.qsort (· < ·) do logInfo m!"  AXIOMS {d}"
#audit_module SimulationExchange.ZeroInt
#audit_module SimulationExchange.ZeroNat
#audit_module SimulationExchange.ZeroGrind
#audit_module SimulationExchange.ZeroRing
#audit_module SimulationExchange.Core
#audit_module SimulationExchange.Model
#audit_module SimulationExchange.Walkers
#audit_module SimulationExchange.Meeting
#audit_module SimulationExchange.Boundary
#audit_module SimulationExchange.Instances
#audit_module SimulationExchange.Switching
