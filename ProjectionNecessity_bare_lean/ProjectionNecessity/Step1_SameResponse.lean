/-
  Projection Necessity, Step 1: the cells of a response map.

  Bare Lean 4, no imports, no tactics. Every proof is a term built from
  `Eq.refl`, `Eq.symm` and `Eq.trans`. Target: zero axioms for every
  theorem (checked by the `#print axioms` lines at the end).

  Setting. A system has states `Φ` and responds through a map
  `r : Φ → R`. Nothing is assumed about `Φ` or `R` yet: no finiteness,
  no symmetry, no dynamics. Those enter in later steps.

  Two states lie in the same cell when the system responds to them
  identically. This step proves only that "same cell" is an equivalence
  relation, so the cells partition `Φ`. The projection of later steps is
  the map that sends a state to its cell.
-/

namespace PrimitiveReflexivity.ProjectionNecessity

/-- Two states are in the same cell when the system responds to them
identically. -/
def SameResponse {Φ R : Type} (r : Φ → R) (a b : Φ) : Prop :=
  r a = r b

/-- Every state is in its own cell. -/
theorem sameResponse_refl {Φ R : Type} (r : Φ → R) (a : Φ) :
    SameResponse r a a :=
  Eq.refl (r a)

/-- Being in the same cell is symmetric. -/
theorem sameResponse_symm {Φ R : Type} (r : Φ → R) {a b : Φ}
    (h : SameResponse r a b) : SameResponse r b a :=
  Eq.symm h

/-- Being in the same cell is transitive. -/
theorem sameResponse_trans {Φ R : Type} (r : Φ → R) {a b c : Φ}
    (hab : SameResponse r a b) (hbc : SameResponse r b c) :
    SameResponse r a c :=
  Eq.trans hab hbc

/-- The three properties together: the cells of any response map
partition the states. -/
theorem sameResponse_equivalence {Φ R : Type} (r : Φ → R) :
    Equivalence (SameResponse r) :=
  { refl  := fun a => sameResponse_refl r a
    symm  := fun h => sameResponse_symm r h
    trans := fun hab hbc => sameResponse_trans r hab hbc }

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.sameResponse_refl
#print axioms PrimitiveReflexivity.ProjectionNecessity.sameResponse_symm
#print axioms PrimitiveReflexivity.ProjectionNecessity.sameResponse_trans
#print axioms PrimitiveReflexivity.ProjectionNecessity.sameResponse_equivalence
