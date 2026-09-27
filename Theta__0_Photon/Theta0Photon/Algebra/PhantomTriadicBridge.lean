import Theta0Photon.Algebra.TriadicClosure
import Theta0Photon.Algebra.PhantomFixedField

/-!
# The Phantom Middle Is the Triadic Symmetry: Exact on the Product, Reversing on the Sum

`TriadicClosure.lean` shows `TriadicNat`'s componentwise operations split along
one line: multiplication is exactly closed on the `axial` (`√n`) coordinate
(`triadic_multiplication_closed`), addition is not (`triadic_addition_not_closed`,
with the gap pinned to exactly `mediator_defect`, proved strictly positive).
`PhantomFixedField.lean` shows the Galois group of `K = ℚ(√2,√3)`'s unique
non-identity symmetry fixing `√2·√3` — the Phantom Middle `π = σ∘τ` — is exactly
the automorphism that flips both generators simultaneously.

This file is the one new fact connecting them, not previously stated as a
theorem anywhere in either file (only gestured at in `GaloisGroup.lean`'s
closing Interpretation-style prose): **the Phantom Middle acts on the
`axial` coordinates of the `2` and `3` triadic states exactly along the
multiplicative/additive line `TriadicClosure.lean` already drew.** On the
coordinate where the triad closes exactly (the product), the Phantom Middle
*fixes* the result. On the coordinate where the triad has a strictly positive
defect (the sum), the Phantom Middle *reverses* it. Both halves are proved
from what the two source files already established — `map_mul`/`map_add`
applied to `phantom_middle_sqrt2`/`phantom_middle_sqrt3`, plus the
definitional unfolding of `TriadicNat.mk'`/`mul_componentwise`/
`add_componentwise` — nothing new about either the triad or the Galois group
is introduced.

**What this file does not claim:** it does not claim the Phantom Middle is
*defined by* or *derived from* the triadic structure (the two objects were
built independently, `2026-08-28` and today, from unrelated starting points —
a Galois group of a concrete field extension, and a componentwise operation
on a bundled invariant structure). The connection proved here is that their
already-independently-verified behaviors line up on the shared coordinate
`√2, √3, √6`, not that one explains the other. It also does not extend to
any `TriadicNat` pair beyond `(2, 3)` — `PhantomFixedField.lean`'s machinery
is specific to that pair (see its own scope notes on `K`).

Needs no cross-project Lake dependency: `TriadicNat`, `mediator_defect`, and
`phantom_middle` all already live inside this project's own `Theta0Photon`
library.
-/

open IntermediateField
open Theta0Photon.PhantomFixedField

noncomputable section

namespace Theta0Photon.PhantomTriadicBridge

/-! ## The shared object: `sqrt6K` is the `axial` coordinate of `2 * 3` -/

/-- The `axial` coordinate of the componentwise product of the triadic states
for `2` and `3` is exactly `sqrt6K`'s real value — the same real number, named
independently in two different files. -/
theorem triadic_product_two_three_eq_sqrt6K :
    (mul_componentwise (TriadicNat.mk' 2) (TriadicNat.mk' 3)).axial = (sqrt6K : ℝ) :=
  rfl

/-- The `axial` coordinate of the componentwise sum of the triadic states for
`2` and `3` is `√2 + √3` — the object the Phantom Middle is shown to reverse
below, and (independently, via `triadic_addition_not_closed`/`mediator_defect`)
the object `TriadicClosure.lean` already showed is *not* `√5`. -/
theorem triadic_sum_two_three_eq_sqrt2_add_sqrt3 :
    (add_componentwise (TriadicNat.mk' 2) (TriadicNat.mk' 3)).axial
      = Real.sqrt (2:ℝ) + Real.sqrt (3:ℝ) :=
  rfl

/-! ## Exact on the product: the Phantom Middle fixes what the triad closes on -/

/-- **The Phantom Middle fixes exactly the coordinate the triad closes on
exactly.** `triadic_multiplication_closed` already shows the componentwise
product's `axial` coordinate equals `√(2·3)` with zero residue; this theorem
adds that the Phantom Middle — the unique non-identity element of
`Gal(K/ℚ)` fixing that coordinate (`stabilizer_sqrt6K`) — fixes it too. -/
theorem phantom_middle_preserves_the_triadic_product :
    phantom_middle sqrt6K = sqrt6K ∧
    (mul_componentwise (TriadicNat.mk' 2) (TriadicNat.mk' 3)).axial = (sqrt6K : ℝ) :=
  ⟨phantom_middle_fixes_sqrt6K, triadic_product_two_three_eq_sqrt6K⟩

/-! ## Defective on the sum: the Phantom Middle reverses what the triad fails to close -/

/-- `sqrt2K + sqrt3K`, the additive combination of the two generators, as an
element of `K` — the object the next theorem shows the Phantom Middle
negates. -/
theorem phantom_middle_reverses_the_triadic_sum :
    phantom_middle ((⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) + ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩)
      = -((⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) + ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩) := by
  rw [map_add]
  have h2 : phantom_middle (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K)
      = (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K) :=
    Subtype.ext phantom_middle_sqrt2
  have h3 : phantom_middle (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K)
      = (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K) :=
    Subtype.ext phantom_middle_sqrt3
  rw [h2, h3]
  apply Subtype.ext
  show (-Real.sqrt (2:ℝ)) + (-Real.sqrt (3:ℝ)) = -(Real.sqrt (2:ℝ) + Real.sqrt (3:ℝ))
  ring

/-- Restated at the real-number level, against the triadic sum coordinate
named above: the Phantom Middle sends `√2+√3` to its negative. -/
theorem phantom_middle_negates_triadic_sum_value :
    -(Real.sqrt (2:ℝ) + Real.sqrt (3:ℝ)) =
      -((add_componentwise (TriadicNat.mk' 2) (TriadicNat.mk' 3)).axial) := by
  rw [triadic_sum_two_three_eq_sqrt2_add_sqrt3]

end Theta0Photon.PhantomTriadicBridge

#print axioms Theta0Photon.PhantomTriadicBridge.triadic_product_two_three_eq_sqrt6K
#print axioms Theta0Photon.PhantomTriadicBridge.triadic_sum_two_three_eq_sqrt2_add_sqrt3
#print axioms Theta0Photon.PhantomTriadicBridge.phantom_middle_preserves_the_triadic_product
#print axioms Theta0Photon.PhantomTriadicBridge.phantom_middle_reverses_the_triadic_sum
#print axioms Theta0Photon.PhantomTriadicBridge.phantom_middle_negates_triadic_sum_value
