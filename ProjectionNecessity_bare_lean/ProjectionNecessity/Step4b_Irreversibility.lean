/-
  Projection Necessity, Step 4b: the projection is irreversible.

  Bare Lean 4. Imports only Steps 3 and 4a of this folder; no Mathlib, no
  Batteries. Proofs are terms plus structural tactics (`obtain`,
  `exact`). No `simp`, `omega`, `decide` or `by_cases`. Target: zero
  axioms for every declaration.

  Hypotheses, neither of which mentions a projection:

  * Finitely many responses. `AtMostResponses k code`: every response
    gets a distinct label below `k`.
  * Infinitely many states. `DistinctStates s`: a sequence of states
    `s 0, s 1, s 2, …` that are pairwise distinct.

  Conclusions, about the projection that Step 3 built from the response
  map:

  * `two_states_share_a_cell`: two distinct states have the same
    projection. Some cell holds more than one state, so a residue exists.
  * `projection_not_reversible`: no map from cells back to states
    recovers every state from its cell.

  This is condition (P3) of `Projection_Formal_Definition.md`, derived
  from finiteness rather than assumed.
-/

import ProjectionNecessity.Step3_Factorization
import ProjectionNecessity.Step4a_Pigeonhole

namespace PrimitiveReflexivity.ProjectionNecessity

/-- **Finitely many responses.** Every response has a label below `k`,
and different responses have different labels. -/
def AtMostResponses {R : Type} (k : Nat) (code : R → Nat) : Prop :=
  (∀ y : R, code y < k) ∧ (∀ y₁ y₂ : R, code y₁ = code y₂ → y₁ = y₂)

/-- **Infinitely many states.** The states `s 0, s 1, s 2, …` are
pairwise distinct. -/
def DistinctStates {Φ : Type} (s : Nat → Φ) : Prop :=
  ∀ i j : Nat, s i = s j → i = j

/-- **A residue exists.** With finitely many responses and infinitely
many states, two distinct states land in the same cell. -/
theorem two_states_share_a_cell {Φ R : Type} (r : Φ → R)
    (k : Nat) (code : R → Nat) (hR : AtMostResponses k code)
    (s : Nat → Φ) (hs : DistinctStates s) :
    ∃ a b : Φ, a ≠ b ∧ project r a = project r b := by
  obtain ⟨i, j, hij, _, hcode⟩ :=
    pigeonhole k (fun n => code (r (s n))) (fun n _ => hR.1 (r (s n)))
  have hresp : SameResponse r (s i) (s j) := hR.2 (r (s i)) (r (s j)) hcode
  exact ⟨s i, s j,
    fun heq => Nat.ne_of_lt hij (hs i j heq),
    project_eq_of_sameResponse r hresp⟩

/-- **Irreversibility (P3).** With finitely many responses and
infinitely many states, no map from cells back to states recovers every
state from its cell. -/
theorem projection_not_reversible {Φ R : Type} (r : Φ → R)
    (k : Nat) (code : R → Nat) (hR : AtMostResponses k code)
    (s : Nat → Φ) (hs : DistinctStates s) :
    ¬ ∃ back : Cell r → Φ, ∀ φ : Φ, back (project r φ) = φ :=
  fun ⟨back, hback⟩ =>
    match two_states_share_a_cell r k code hR s hs with
    | ⟨a, b, hab, hproj⟩ =>
      hab (Eq.trans (Eq.symm (hback a))
            (Eq.trans (congrArg back hproj) (hback b)))

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.two_states_share_a_cell
#print axioms PrimitiveReflexivity.ProjectionNecessity.projection_not_reversible
