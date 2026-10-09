import Theta0Photon.Algebra.TriadicClosure
import Theta0Photon.Algebra.GeneralPhantomFixedField
import Theta0Photon.Algebra.PhantomTriadicBridge

/-!
# General Phantom Triadic Bridge: Exact on the Product, Reversing on the Sum,
for any independent pair

`PhantomTriadicBridge.lean` connects `TriadicClosure.lean`'s triadic
multiplicative/additive split to `PhantomFixedField.lean`'s Phantom Middle,
for the fixed pair `(2,3)`. This file reruns that connection for an arbitrary
pair `d₁ d₂ : ℕ` satisfying the independence condition:

* `¬ IsSquare d₁`
* `¬ IsSquare d₂`
* `¬ IsSquare (d₁ * d₂)`

As `TriadicClosure.lean`'s own module doc already establishes,
`TriadicNat.mk'`, `mul_componentwise`, and `add_componentwise` are general in
`n` — no change needed there. The only thing `PhantomTriadicBridge.lean`
actually specialized to `(2,3)` was which Phantom Middle and which fixed
object it compared the triad against; both are now
`GeneralGaloisGroup.phantom_middle hd1 hd2 hd12` and
`GeneralPhantomFixedField.sqrt_prod_K`, so this file is close to pure wiring,
exactly as `ROADMAP_LEDGER.md` anticipated. The `(2,3)` case is recovered
exactly as a sanity check at the end, checked against
`PhantomTriadicBridge.lean`'s own two bridge theorems.
-/

open Theta0Photon.GeneralFieldTower
open Theta0Photon.GeneralGaloisGroup
open Theta0Photon.GeneralPhantomFixedField

noncomputable section

namespace Theta0Photon.GeneralPhantomTriadicBridge

variable {d₁ d₂ : ℕ}

/-! ## The shared object: `sqrt_prod_K` is the `axial` coordinate of `d₁ * d₂` -/

/-- The `axial` coordinate of the componentwise product of the triadic states
for `d₁` and `d₂` is exactly `sqrt_prod_K`'s real value — the same real
number, named independently in two different files. No hypotheses needed:
both sides reduce to `√d₁ · √d₂` definitionally. -/
theorem triadic_product_eq_sqrt_prod_K :
    (mul_componentwise (TriadicNat.mk' d₁) (TriadicNat.mk' d₂)).axial
      = ((sqrt_prod_K : K d₁ d₂) : ℝ) :=
  rfl

/-- The `axial` coordinate of the componentwise sum of the triadic states for
`d₁` and `d₂` is `√d₁ + √d₂` — the object the Phantom Middle is shown to
reverse below. -/
theorem triadic_sum_eq_sqrt_d1_add_sqrt_d2 :
    (add_componentwise (TriadicNat.mk' d₁) (TriadicNat.mk' d₂)).axial
      = Real.sqrt (d₁ : ℝ) + Real.sqrt (d₂ : ℝ) :=
  rfl

/-! ## Exact on the product: the Phantom Middle fixes what the triad closes on -/

/-- **The Phantom Middle fixes exactly the coordinate the triad closes on
exactly.** `triadic_multiplication_closed` already shows the componentwise
product's `axial` coordinate equals `√(d₁·d₂)` with zero residue; this
theorem adds that the Phantom Middle — the unique non-identity element of
`Gal(K d₁ d₂/ℚ)` fixing that coordinate (`stabilizer_sqrt_prod`) — fixes it
too. -/
theorem phantom_middle_preserves_the_triadic_product
    (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    phantom_middle hd1 hd2 hd12 sqrt_prod_K = sqrt_prod_K ∧
    (mul_componentwise (TriadicNat.mk' d₁) (TriadicNat.mk' d₂)).axial
      = ((sqrt_prod_K : K d₁ d₂) : ℝ) :=
  ⟨phantom_middle_fixes_sqrt_prod hd1 hd2 hd12, triadic_product_eq_sqrt_prod_K⟩

/-! ## Defective on the sum: the Phantom Middle reverses what the triad fails to close -/

/-- `⟨√d₁⟩ + ⟨√d₂⟩`, the additive combination of the two generators, as an
element of `K d₁ d₂` — the object the next theorem shows the Phantom Middle
negates. -/
theorem phantom_middle_reverses_the_triadic_sum
    (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    phantom_middle hd1 hd2 hd12
        ((⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) + ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩)
      = -((⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) + ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩) := by
  rw [map_add]
  have h1 : phantom_middle hd1 hd2 hd12 (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂)
      = (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (phantom_middle_sqrt_d1 hd1 hd2 hd12)
  have h2 : phantom_middle hd1 hd2 hd12 (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂)
      = (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (phantom_middle_sqrt_d2 hd1 hd2 hd12)
  rw [h1, h2]
  apply Subtype.ext
  show (-Real.sqrt (d₁ : ℝ)) + (-Real.sqrt (d₂ : ℝ)) = -(Real.sqrt (d₁ : ℝ) + Real.sqrt (d₂ : ℝ))
  ring

/-- Restated at the real-number level, against the triadic sum coordinate
named above: the Phantom Middle sends `√d₁+√d₂` to its negative. -/
theorem phantom_middle_negates_triadic_sum_value :
    -(Real.sqrt (d₁ : ℝ) + Real.sqrt (d₂ : ℝ)) =
      -((add_componentwise (TriadicNat.mk' d₁) (TriadicNat.mk' d₂)).axial) := by
  rw [triadic_sum_eq_sqrt_d1_add_sqrt_d2]

/-! ## Sanity check: specializes to the `(2,3)` instance -/

/-- Reruns `PhantomTriadicBridge.lean`'s own
`phantom_middle_preserves_the_triadic_product` through this file's general
theorem, at `(d₁,d₂) = (2,3)`. -/
theorem phantom_middle_preserves_the_triadic_product_at_2_3 :
    phantom_middle
        (not_isSquare_of_not_exists_sq two_not_square)
        (not_isSquare_of_not_exists_sq three_not_square)
        (not_isSquare_of_not_exists_sq six_not_square)
        (sqrt_prod_K (d₁ := 2) (d₂ := 3)) = sqrt_prod_K (d₁ := 2) (d₂ := 3) ∧
    (mul_componentwise (TriadicNat.mk' 2) (TriadicNat.mk' 3)).axial
      = ((sqrt_prod_K (d₁ := 2) (d₂ := 3) : _root_.K) : ℝ) :=
  phantom_middle_preserves_the_triadic_product
    (not_isSquare_of_not_exists_sq two_not_square)
    (not_isSquare_of_not_exists_sq three_not_square)
    (not_isSquare_of_not_exists_sq six_not_square)

/-- Reruns `PhantomTriadicBridge.lean`'s own
`phantom_middle_reverses_the_triadic_sum` through this file's general
theorem, at `(d₁,d₂) = (2,3)`. -/
theorem phantom_middle_reverses_the_triadic_sum_at_2_3 :
    phantom_middle
        (not_isSquare_of_not_exists_sq two_not_square)
        (not_isSquare_of_not_exists_sq three_not_square)
        (not_isSquare_of_not_exists_sq six_not_square)
        ((⟨Real.sqrt (2:ℝ), sqrt_d1_mem_K⟩ : _root_.K) + ⟨Real.sqrt (3:ℝ), sqrt_d2_mem_K⟩)
      = -((⟨Real.sqrt (2:ℝ), sqrt_d1_mem_K⟩ : _root_.K) + ⟨Real.sqrt (3:ℝ), sqrt_d2_mem_K⟩) :=
  phantom_middle_reverses_the_triadic_sum
    (not_isSquare_of_not_exists_sq two_not_square)
    (not_isSquare_of_not_exists_sq three_not_square)
    (not_isSquare_of_not_exists_sq six_not_square)

end Theta0Photon.GeneralPhantomTriadicBridge

end

#print axioms Theta0Photon.GeneralPhantomTriadicBridge.triadic_product_eq_sqrt_prod_K
#print axioms Theta0Photon.GeneralPhantomTriadicBridge.phantom_middle_preserves_the_triadic_product
#print axioms Theta0Photon.GeneralPhantomTriadicBridge.phantom_middle_reverses_the_triadic_sum
#print axioms Theta0Photon.GeneralPhantomTriadicBridge.phantom_middle_negates_triadic_sum_value
#print axioms Theta0Photon.GeneralPhantomTriadicBridge.phantom_middle_preserves_the_triadic_product_at_2_3
#print axioms Theta0Photon.GeneralPhantomTriadicBridge.phantom_middle_reverses_the_triadic_sum_at_2_3
