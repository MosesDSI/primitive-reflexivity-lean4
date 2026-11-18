/-
  Projection Necessity, Step 5: the projection inherits the system's
  symmetry.

  Bare Lean 4. Imports only Step 3 of this folder. Proofs are terms built
  from `Eq.refl`, `Eq.symm`, `Eq.trans`, `congrArg` and pattern matching.
  No tactics. Target: zero axioms for every declaration.

  Hypothesis, which mentions no projection: a symmetry of the system.
  `σ : Φ → Φ` acts on states, `τ : R → R` acts on responses, and the
  response map respects them:

      `Equivariant r σ τ`  :=  ∀ φ, r (σ φ) = τ (r φ).

  Mirroring a state mirrors its response. (For the walkers: `σ` flips a
  walker, `τ` swaps `above` and `below`, as in `flip_inverts_side`.)

  Conclusions, about the projection that Step 3 built from `r`:

  * `sameResponse_map`: the symmetry sends cells to cells.
  * `cellMap`: so it induces a map on cells, and
    `project_equivariant`: projecting a mirrored state is mirroring its
    cell. The projection commutes with the symmetry.
  * `cellMap_unique`: any map on cells that commutes with the projection
    in this way agrees with `cellMap` on every cell. The symmetry of the
    cells is forced by the symmetry of the system, not chosen.
  * `project_invariant_iff`: in the special case where the symmetry
    leaves responses unchanged, the projection is invariant exactly
    when the response is.

  So invariance of the projection is a theorem, inherited from the
  system, not part of the definition of a projection.
-/

import ProjectionNecessity.Step3_Factorization

namespace PrimitiveReflexivity.ProjectionNecessity

/-- **A symmetry of the system.** Mirroring a state by `σ` mirrors its
response by `τ`. -/
def Equivariant {Φ R : Type} (r : Φ → R) (σ : Φ → Φ) (τ : R → R) : Prop :=
  ∀ φ : Φ, r (σ φ) = τ (r φ)

/-- **The symmetry sends cells to cells.** If two states are in the
same cell, so are their mirror images. -/
theorem sameResponse_map {Φ R : Type} {r : Φ → R} {σ : Φ → Φ}
    {τ : R → R} (hσ : Equivariant r σ τ) {a b : Φ}
    (hab : SameResponse r a b) : SameResponse r (σ a) (σ b) :=
  Eq.trans (hσ a) (Eq.trans (congrArg τ hab) (Eq.symm (hσ b)))

/-- **The induced map on cells.** The cell with response `y` goes to the
cell with response `τ y`. That cell exists: if state `φ` produces `y`,
then `σ φ` produces `τ y`. -/
def cellMap {Φ R : Type} {r : Φ → R} {σ : Φ → Φ} {τ : R → R}
    (hσ : Equivariant r σ τ) (c : Cell r) : Cell r :=
  ⟨τ c.val,
    match c.property with
    | ⟨φ, hφ⟩ => ⟨σ φ, Eq.trans (hσ φ) (congrArg τ hφ)⟩⟩

/-- **The projection commutes with the symmetry.** Projecting a mirrored
state gives the mirrored cell. -/
theorem project_equivariant {Φ R : Type} {r : Φ → R} {σ : Φ → Φ}
    {τ : R → R} (hσ : Equivariant r σ τ) (φ : Φ) :
    project r (σ φ) = cellMap hσ (project r φ) :=
  cell_ext (hσ φ)

/-- **The symmetry on cells is forced.** Any map `M` on cells that
commutes with the projection (`project (σ φ) = M (project φ)`) agrees
with `cellMap` on every cell. -/
theorem cellMap_unique {Φ R : Type} {r : Φ → R} {σ : Φ → Φ}
    {τ : R → R} (hσ : Equivariant r σ τ) (M : Cell r → Cell r)
    (hM : ∀ φ : Φ, project r (σ φ) = M (project r φ)) :
    ∀ c : Cell r, M c = cellMap hσ c :=
  fun c =>
    match project_surjective r c with
    | ⟨φ, hφ⟩ =>
      Eq.trans (Eq.symm (congrArg M hφ))
        (Eq.trans (Eq.symm (hM φ))
          (Eq.trans (project_equivariant hσ φ) (congrArg (cellMap hσ) hφ)))

/-- **Invariant response gives invariant projection.** If the symmetry
leaves every response unchanged, it leaves every cell unchanged. -/
theorem project_invariant {Φ R : Type} {r : Φ → R} {σ : Φ → Φ}
    (hσ : ∀ φ : Φ, r (σ φ) = r φ) (φ : Φ) :
    project r (σ φ) = project r φ :=
  cell_ext (hσ φ)

/-- **Invariance is inherited in both directions.** The projection is
invariant under `σ` exactly when the response is. -/
theorem project_invariant_iff {Φ R : Type} (r : Φ → R) (σ : Φ → Φ) :
    (∀ φ : Φ, project r (σ φ) = project r φ) ↔ (∀ φ : Φ, r (σ φ) = r φ) :=
  ⟨fun h φ => congrArg Subtype.val (h φ), fun h φ => project_invariant h φ⟩

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.sameResponse_map
#print axioms PrimitiveReflexivity.ProjectionNecessity.cellMap
#print axioms PrimitiveReflexivity.ProjectionNecessity.project_equivariant
#print axioms PrimitiveReflexivity.ProjectionNecessity.cellMap_unique
#print axioms PrimitiveReflexivity.ProjectionNecessity.project_invariant
#print axioms PrimitiveReflexivity.ProjectionNecessity.project_invariant_iff
