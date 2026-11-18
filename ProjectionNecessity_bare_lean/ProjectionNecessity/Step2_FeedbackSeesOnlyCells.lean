/-
  Projection Necessity, Step 2: feedback sees only cells.

  Bare Lean 4. Imports only Step 1. No tactics. Every proof is a term
  built from `congrArg`, `Eq.symm`, `Eq.trans` and pattern matching on
  `Exists`. Target: zero axioms for every theorem.

  Setting, as in Step 1: states `Φ`, a response map `r : Φ → R`, and
  cells given by `SameResponse r` (defined in Step 1).

  New in this step: feedback. A loop acts on the system through what it
  read, never through the state directly. We state this two ways.

  * `DependsOnlyOnResponse r f`: some `g` exists with `f φ = g (r φ)`
    for every state. This is "f reads the state only through r".
  * A closed-loop step `F φ (act (r φ))`: the next state may depend on
    the full state `φ`, but the feedback contribution `act (r φ)` is
    computed from the response alone.

  The result in both forms: two states in the same cell receive the
  same feedback. Whatever distinguishes them inside a cell (the residue)
  is invisible to the loop.
-/

import ProjectionNecessity.Step1_SameResponse

namespace PrimitiveReflexivity.ProjectionNecessity

/-- `f` reads the state only through the response `r`: it is some
function of the response. -/
def DependsOnlyOnResponse {Φ R A : Type} (r : Φ → R) (f : Φ → A) : Prop :=
  ∃ g : R → A, ∀ φ : Φ, f φ = g (r φ)

/-- A controller applied to the response is a function of the response.
(The trivial witness: `g` is the controller itself.) -/
theorem controller_dependsOnlyOnResponse {Φ R A : Type}
    (r : Φ → R) (act : R → A) :
    DependsOnlyOnResponse r (fun φ => act (r φ)) :=
  ⟨act, fun φ => Eq.refl (act (r φ))⟩

/-- **Feedback sees only cells.** Anything that reads the state only
through the response takes the same value on two states in the same
cell. -/
theorem constant_on_cells {Φ R A : Type} (r : Φ → R) (f : Φ → A)
    (hf : DependsOnlyOnResponse r f) {a b : Φ}
    (hab : SameResponse r a b) : f a = f b :=
  match hf with
  | ⟨g, hg⟩ => Eq.trans (hg a) (Eq.trans (congrArg g hab) (Eq.symm (hg b)))

/-- **Closed-loop form.** In a step `F φ (act (r φ))`, two states in the
same cell receive the same feedback `act (r φ)`, however different the
states themselves are. -/
theorem same_cell_same_feedback {Φ R A : Type}
    (r : Φ → R) (act : R → A) {a b : Φ}
    (hab : SameResponse r a b) : act (r a) = act (r b) :=
  constant_on_cells r (fun φ => act (r φ))
    (controller_dependsOnlyOnResponse r act) hab

/-- **Residue blindness.** If two states in the same cell are fed back
through a step that depends on the state only through the response,
their next states are equal. A loop of this kind cannot separate states
the response does not separate. -/
theorem same_cell_same_next_state {Φ R : Type}
    (r : Φ → R) (G : R → Φ) {a b : Φ}
    (hab : SameResponse r a b) : G (r a) = G (r b) :=
  congrArg G hab

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.controller_dependsOnlyOnResponse
#print axioms PrimitiveReflexivity.ProjectionNecessity.constant_on_cells
#print axioms PrimitiveReflexivity.ProjectionNecessity.same_cell_same_feedback
#print axioms PrimitiveReflexivity.ProjectionNecessity.same_cell_same_next_state
