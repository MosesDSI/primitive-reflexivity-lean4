/-
  Projection Necessity, Step 3: the loop factors through a projection.

  Bare Lean 4. Imports only Step 2 (with Step 1). No tactics. Proofs are
  terms built from
  `Eq.refl`, `Eq.symm`, `Eq.trans`, `congrArg` and pattern matching
  (including on `rfl`). Target: zero axioms for every theorem.

  No quotient types are used, because `Quot.sound` is an axiom. A cell is
  represented by its response value instead: `Cell r` is the subtype of
  responses that some state actually produces. `Subtype` comes from Lean's
  core library; this file declares no `structure` of its own, so it
  generates no `mk.injEq` lemmas.

  What is constructed and proved, from the response map `r` alone:

  * `project r : Φ → Cell r`, the projection of a state onto its cell.
  * It is onto (`project_surjective`).
  * Its fibres are exactly the cells of Step 1 (`project_eq_iff`).
  * Anything that reads the state only through `r` factors as
    "project first, then act on the cell" (`factorization`), and that
    factor is unique (`factorization_unique`).

  So the projection is not assumed: it is built from the response map,
  and every response-only loop necessarily passes through it.

  `SameResponse` (Step 1) and `DependsOnlyOnResponse` (Step 2) come from
  the imports.
-/

import ProjectionNecessity.Step2_FeedbackSeesOnlyCells

namespace PrimitiveReflexivity.ProjectionNecessity

/-- The cells of `r`, each named by its response value: the responses
that some state actually produces. -/
abbrev Cell {Φ R : Type} (r : Φ → R) : Type :=
  { y : R // ∃ φ : Φ, r φ = y }

/-- **The projection.** Send a state to its cell. -/
def project {Φ R : Type} (r : Φ → R) (φ : Φ) : Cell r :=
  ⟨r φ, ⟨φ, Eq.refl (r φ)⟩⟩

/-- Two cells are equal when they have the same response value.
(Proved by matching on `rfl`; the two existence proofs are equal by
Lean's definitional proof irrelevance, which is not an axiom.) -/
theorem cell_ext {Φ R : Type} {r : Φ → R} :
    ∀ {c d : Cell r}, c.val = d.val → c = d
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- **Every cell is reached.** The projection is onto. -/
theorem project_surjective {Φ R : Type} (r : Φ → R) :
    ∀ c : Cell r, ∃ φ : Φ, project r φ = c
  | ⟨_, ⟨φ, rfl⟩⟩ => ⟨φ, rfl⟩

/-- States in the same cell have the same projection. -/
theorem project_eq_of_sameResponse {Φ R : Type} (r : Φ → R) {a b : Φ}
    (hab : SameResponse r a b) : project r a = project r b :=
  cell_ext hab

/-- States with the same projection are in the same cell. -/
theorem sameResponse_of_project_eq {Φ R : Type} (r : Φ → R) {a b : Φ}
    (h : project r a = project r b) : SameResponse r a b :=
  congrArg Subtype.val h

/-- **The fibres of the projection are exactly the cells.** -/
theorem project_eq_iff {Φ R : Type} (r : Φ → R) (a b : Φ) :
    project r a = project r b ↔ SameResponse r a b :=
  ⟨sameResponse_of_project_eq r, project_eq_of_sameResponse r⟩

/-- **Factorization.** Anything that reads the state only through the
response is "project first, then act on the cell". -/
theorem factorization {Φ R A : Type} (r : Φ → R) (f : Φ → A)
    (hf : DependsOnlyOnResponse r f) :
    ∃ h : Cell r → A, ∀ φ : Φ, f φ = h (project r φ) :=
  match hf with
  | ⟨g, hg⟩ => ⟨fun c => g c.val, hg⟩

/-- **The factor is unique.** Two maps on cells that both factor `f`
agree on every cell. -/
theorem factorization_unique {Φ R A : Type} (r : Φ → R) (f : Φ → A)
    (h₁ h₂ : Cell r → A)
    (hf₁ : ∀ φ : Φ, f φ = h₁ (project r φ))
    (hf₂ : ∀ φ : Φ, f φ = h₂ (project r φ)) :
    ∀ c : Cell r, h₁ c = h₂ c :=
  fun c =>
    match project_surjective r c with
    | ⟨φ, hφ⟩ =>
      Eq.trans (Eq.symm (congrArg h₁ hφ))
        (Eq.trans (Eq.trans (Eq.symm (hf₁ φ)) (hf₂ φ)) (congrArg h₂ hφ))

/-- **Closed-loop form.** A loop whose next state depends only on the
response is the projection followed by a step on cells. -/
theorem loop_factors_through_projection {Φ R : Type}
    (r : Φ → R) (G : R → Φ) :
    ∃ H : Cell r → Φ, ∀ φ : Φ, G (r φ) = H (project r φ) :=
  factorization r (fun φ => G (r φ)) ⟨G, fun φ => Eq.refl (G (r φ))⟩

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.cell_ext
#print axioms PrimitiveReflexivity.ProjectionNecessity.project_surjective
#print axioms PrimitiveReflexivity.ProjectionNecessity.project_eq_of_sameResponse
#print axioms PrimitiveReflexivity.ProjectionNecessity.sameResponse_of_project_eq
#print axioms PrimitiveReflexivity.ProjectionNecessity.project_eq_iff
#print axioms PrimitiveReflexivity.ProjectionNecessity.factorization
#print axioms PrimitiveReflexivity.ProjectionNecessity.factorization_unique
#print axioms PrimitiveReflexivity.ProjectionNecessity.loop_factors_through_projection
