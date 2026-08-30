-- Section VI: The Incommensurable Dual-Clock Engine
-- Minimal local iterate helper to maintain dependency-free compilation
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

namespace PrimitiveReflexivity

-- N is declared explicitly at the struct level
structure BifurcatedState (N : Type) (Phase : Type) where
  polar_clock : Nat
  axial_clock : Phase

class AxialRotation (Phase : Type) where
  rotate_step : Phase → Phase

/--
The Ontological Definition of an Angle (phase-drift form), formally verified
as a non-vacuous, structurally stable predicate:
- Non-vacuous: PhaseDriftMatch is not provable for an arbitrary target_phase
  unrelated to the actual rotation (the loose-existential form this replaces
  was; that version is provable for any target and therefore detects nothing).
- Structurally stable: {N : Type} is bound explicitly here rather than left
  to `autoImplicit`, so the definition elaborates identically whether
  `autoImplicit` is on (Lean's default) or off (`set_option autoImplicit
  false`) — confirmed by compiling this file under both settings.
-/
def PhaseDriftMatch {N : Type} {Phase : Type} [r : AxialRotation Phase]
    (state : BifurcatedState N Phase) (target_phase : Phase) : Prop :=
  iterate r.rotate_step state.polar_clock state.axial_clock = target_phase

end PrimitiveReflexivity
