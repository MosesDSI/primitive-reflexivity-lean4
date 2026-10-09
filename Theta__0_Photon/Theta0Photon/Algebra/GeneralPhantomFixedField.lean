import Theta0Photon.Algebra.GeneralGaloisGroup
import Theta0Photon.Algebra.PhantomFixedField

/-!
# General Phantom Fixed Field: `Fix(π) = ℚ(√d₁·√d₂)` for any independent pair

`PhantomFixedField.lean` shows the Phantom Middle's fixed field is exactly
`ℚ(√2·√3)` for the fixed pair `K = ℚ(√2,√3)`. This file reruns that
construction — same shape, same `map_mul`-pushed-through-flip-lemmas
argument — for an arbitrary pair `d₁ d₂ : ℕ` satisfying:

* `¬ IsSquare d₁`
* `¬ IsSquare d₂`
* `¬ IsSquare (d₁ * d₂)`

built on `GeneralGaloisGroup.lean`'s already-general `sigma_K`, `tau_K`,
`phantom_middle`, `card_Gal_eq_four` instead of `GaloisGroup.lean`'s
`(2,3)`-specific versions, and `GeneralFieldTower.lean`'s `sqrt_sqrt_finrank`
instead of `FieldTower.lean`'s `sqrt2_sqrt3_finrank`.

No new mathematical content: every step is `PhantomFixedField.lean`'s own
argument with `2 ↦ d₁`, `3 ↦ d₂`, `6 ↦ d₁·d₂`. The `(2,3)` case is recovered
exactly as a sanity check at the end of this file, checked against
`PhantomFixedField.lean`'s own `stabilizer_sqrt6K` and
`fixedField_phantom_middle` — not just a matching numeral, but the same
object.
-/

open Polynomial IntermediateField
open Theta0Photon.GeneralFieldTower
open Theta0Photon.GeneralGaloisGroup

noncomputable section

namespace Theta0Photon.GeneralPhantomFixedField

variable {d₁ d₂ : ℕ}

/-! ## Setup -/

theorem sqrt_prod_mem_K : Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ) ∈ (K d₁ d₂ : IntermediateField ℚ ℝ) :=
  mul_mem sqrt_d1_mem_K sqrt_d2_mem_K

/-- The product of the two generators, `√d₁ · √d₂`, as an element of `K d₁ d₂`. -/
def sqrt_prod_K : K d₁ d₂ := ⟨Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ), sqrt_prod_mem_K⟩

@[simp] theorem sqrt_prod_K_coe :
    (sqrt_prod_K : K d₁ d₂) = Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ) := rfl

theorem sqrt_prod_K_pos (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) :
    (0:ℝ) < (sqrt_prod_K : K d₁ d₂) :=
  mul_pos (sqrt_d1_pos hd1) (sqrt_d2_pos hd2)

/-- The product is not its own negative (it is nonzero). -/
theorem sqrt_prod_K_ne_neg (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) :
    (sqrt_prod_K : K d₁ d₂) ≠ -sqrt_prod_K := by
  intro h
  have hcoe : ((sqrt_prod_K : K d₁ d₂) : ℝ) = -((sqrt_prod_K : K d₁ d₂) : ℝ) :=
    congrArg (fun y : K d₁ d₂ => (y : ℝ)) h
  linarith [sqrt_prod_K_pos hd1 hd2]

/-! ## A. The Phantom Middle fixes the product; each single flip negates it -/

theorem sqrt_prod_K_eq_mul :
    (sqrt_prod_K : K d₁ d₂)
      = (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) * (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂) :=
  rfl

/-- `sqrt_prod_K * sqrt_prod_K = (d₁*d₂ : K d₁ d₂)`. -/
theorem sqrt_prod_K_mul_self :
    (sqrt_prod_K : K d₁ d₂) * sqrt_prod_K = ((d₁ * d₂ : ℕ) : K d₁ d₂) := by
  apply Subtype.ext
  show Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ) * (Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ))
      = (((d₁ * d₂ : ℕ) : K d₁ d₂) : ℝ)
  have hcast : (((d₁ * d₂ : ℕ) : K d₁ d₂) : ℝ) = ((d₁ * d₂ : ℕ) : ℝ) := by norm_cast
  have h1 : Real.sqrt (d₁ : ℝ) * Real.sqrt (d₁ : ℝ) = (d₁ : ℝ) := by
    have := Real.sq_sqrt (Nat.cast_nonneg d₁ : (0:ℝ) ≤ d₁); rwa [sq] at this
  have h2 : Real.sqrt (d₂ : ℝ) * Real.sqrt (d₂ : ℝ) = (d₂ : ℝ) := by
    have := Real.sq_sqrt (Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂); rwa [sq] at this
  rw [hcast]
  calc Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ) * (Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ))
      = Real.sqrt (d₁ : ℝ) * Real.sqrt (d₁ : ℝ) * (Real.sqrt (d₂ : ℝ) * Real.sqrt (d₂ : ℝ)) := by ring
    _ = (d₁ : ℝ) * (d₂ : ℝ) := by rw [h1, h2]
    _ = ((d₁ * d₂ : ℕ) : ℝ) := by push_cast; ring

theorem phantom_middle_fixes_sqrt_prod (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    phantom_middle hd1 hd2 hd12 sqrt_prod_K = sqrt_prod_K := by
  rw [sqrt_prod_K_eq_mul, map_mul]
  have h1 : phantom_middle hd1 hd2 hd12 (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂)
      = (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (phantom_middle_sqrt_d1 hd1 hd2 hd12)
  have h2 : phantom_middle hd1 hd2 hd12 (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂)
      = (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (phantom_middle_sqrt_d2 hd1 hd2 hd12)
  rw [h1, h2]
  apply Subtype.ext
  show (-Real.sqrt (d₁ : ℝ)) * (-Real.sqrt (d₂ : ℝ)) = Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ)
  ring

theorem sigma_negates_sqrt_prod (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    sigma_K hd1 hd2 hd12 sqrt_prod_K = -sqrt_prod_K := by
  rw [sqrt_prod_K_eq_mul, map_mul]
  have h1 : sigma_K hd1 hd2 hd12 (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂)
      = (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (sigma_flips_sqrt_d1 hd1 hd2 hd12)
  have h2 : sigma_K hd1 hd2 hd12 (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂)
      = (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (sigma_fixes_sqrt_d2 hd1 hd2 hd12)
  rw [h1, h2]
  apply Subtype.ext
  show (-Real.sqrt (d₁ : ℝ)) * Real.sqrt (d₂ : ℝ) = -(Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ))
  ring

theorem tau_negates_sqrt_prod (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    tau_K hd1 hd2 hd12 sqrt_prod_K = -sqrt_prod_K := by
  rw [sqrt_prod_K_eq_mul, map_mul]
  have h1 : tau_K hd1 hd2 hd12 (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂)
      = (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (tau_fixes_sqrt_d1 hd1 hd2 hd12)
  have h2 : tau_K hd1 hd2 hd12 (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂)
      = (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (tau_flips_sqrt_d2 hd1 hd2 hd12)
  rw [h1, h2]
  apply Subtype.ext
  show Real.sqrt (d₁ : ℝ) * (-Real.sqrt (d₂ : ℝ)) = -(Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ))
  ring

/-! ## B. Exactly the identity and the Phantom Middle preserve the product -/

theorem stabilizer_sqrt_prod (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) (g : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) :
    g sqrt_prod_K = sqrt_prod_K ↔ g = 1 ∨ g = phantom_middle hd1 hd2 hd12 := by
  constructor
  · intro hg
    have hmem : g ∈ ({1, sigma_K hd1 hd2 hd12, tau_K hd1 hd2 hd12, phantom_middle hd1 hd2 hd12} :
        Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)) := by
      rw [four_elts_eq_univ hd1 hd2 hd12]; exact Finset.mem_univ g
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exfalso
      rw [h, sigma_negates_sqrt_prod hd1 hd2 hd12] at hg
      exact sqrt_prod_K_ne_neg hd1 hd2 hg.symm
    · exfalso
      rw [h, tau_negates_sqrt_prod hd1 hd2 hd12] at hg
      exact sqrt_prod_K_ne_neg hd1 hd2 hg.symm
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]; rfl
    · rw [h]; exact phantom_middle_fixes_sqrt_prod hd1 hd2 hd12

/-! ## D. Galois form: the fixed field of the Phantom Middle is `ℚ(√d₁·√d₂)` -/

theorem mem_fixedField_zpowers_phantom_iff (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) (x : K d₁ d₂) :
    x ∈ IntermediateField.fixedField (Subgroup.zpowers (phantom_middle hd1 hd2 hd12)) ↔
      phantom_middle hd1 hd2 hd12 x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h (phantom_middle hd1 hd2 hd12) (Subgroup.mem_zpowers (phantom_middle hd1 hd2 hd12))
  · intro h f hf
    have hmem : phantom_middle hd1 hd2 hd12
        ∈ MulAction.stabilizer ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h
    have := (Subgroup.zpowers_le.mpr hmem) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this

theorem orderOf_phantom_middle (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    orderOf (phantom_middle hd1 hd2 hd12) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (phantom_sq hd1 hd2 hd12) (Ne.symm (one_ne_phantom hd1 hd2 hd12))

theorem card_zpowers_phantom_middle (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Nat.card (Subgroup.zpowers (phantom_middle hd1 hd2 hd12)) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, orderOf_phantom_middle hd1 hd2 hd12]

theorem sqrt_prod_K_isIntegral : IsIntegral ℚ (sqrt_prod_K : K d₁ d₂) := by
  refine ⟨X ^ 2 - C ((d₁ * d₂ : ℕ) : ℚ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_natCast, sq, sqrt_prod_K_mul_self, sub_self]

theorem sqrt_prod_K_minpoly (hd12 : ¬ IsSquare (d₁ * d₂)) :
    X ^ 2 - C ((d₁ * d₂ : ℕ) : ℚ) = minpoly ℚ (sqrt_prod_K : K d₁ d₂) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact triadic_ground_irreducible (d₁ * d₂) (not_exists_sq_of_not_isSquare hd12)
  · rw [map_sub, map_pow, aeval_X, aeval_C, map_natCast, sq, sqrt_prod_K_mul_self, sub_self]
  · exact monic_X_pow_sub_C _ two_ne_zero

theorem sqrt_prod_K_finrank (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂))) = 2 := by
  rw [IntermediateField.adjoin.finrank sqrt_prod_K_isIntegral, ← sqrt_prod_K_minpoly hd12,
    natDegree_X_pow_sub_C]

theorem fixedField_phantom_middle (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    IntermediateField.fixedField (Subgroup.zpowers (phantom_middle hd1 hd2 hd12)) =
      IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂)) := by
  have hle : (IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂))) ≤
      IntermediateField.fixedField (Subgroup.zpowers (phantom_middle hd1 hd2 hd12)) :=
    IntermediateField.adjoin_simple_le_iff.mpr
      ((mem_fixedField_zpowers_phantom_iff hd1 hd2 hd12 sqrt_prod_K).mpr
        (phantom_middle_fixes_sqrt_prod hd1 hd2 hd12))
  have htower := Module.finrank_mul_finrank ℚ
    (IntermediateField.fixedField (Subgroup.zpowers (phantom_middle hd1 hd2 hd12))) (K d₁ d₂)
  rw [IntermediateField.finrank_fixedField_eq_card, card_zpowers_phantom_middle hd1 hd2 hd12,
    sqrt_sqrt_finrank hd1 hd2 hd12] at htower
  have hfinrank : Module.finrank ℚ
      (IntermediateField.fixedField (Subgroup.zpowers (phantom_middle hd1 hd2 hd12))) = 2 := by
    omega
  exact (IntermediateField.eq_of_le_of_finrank_eq hle
    ((sqrt_prod_K_finrank hd12).trans hfinrank.symm)).symm

/-! ## C. Elementwise form: the fixed elements are exactly `a + b·√d₁·√d₂` -/

theorem sqrt_prod_K_basis_indep (hd12 : ¬ IsSquare (d₁ * d₂)) :
    LinearIndependent ℚ
      (![1, AdjoinSimple.gen ℚ (sqrt_prod_K : K d₁ d₂)] :
        Fin 2 → IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂))) := by
  rw [LinearIndependent.pair_iff' one_ne_zero]
  intro a ha
  have hK : (a : K d₁ d₂) = sqrt_prod_K := by
    have h := congrArg
      (fun y : IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂)) => (y : K d₁ d₂)) ha
    simpa [Algebra.smul_def, AdjoinSimple.coe_gen] using h
  have hR : (a : ℝ) = Real.sqrt ((d₁ * d₂ : ℕ) : ℝ) := by
    have h := congrArg (fun y : K d₁ d₂ => (y : ℝ)) hK
    rw [sqrt_prod_K_coe] at h
    have hmul : Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ) = Real.sqrt ((d₁ * d₂ : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg d₁)]
      norm_cast
    rw [hmul] at h
    exact_mod_cast h
  exact sqrt_ne_ratCast (d₁ * d₂) (not_exists_sq_of_not_isSquare hd12) a hR

def sqrt_prod_K_basis (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Module.Basis (Fin 2) ℚ (IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂))) :=
  basisOfLinearIndependentOfCardEqFinrank (sqrt_prod_K_basis_indep hd12)
    (by simp [sqrt_prod_K_finrank hd12])

theorem sqrt_prod_K_field_eq (hd12 : ¬ IsSquare (d₁ * d₂))
    (x : IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂))) :
    ∃ a c : ℚ, (x : K d₁ d₂) = (a : K d₁ d₂) + (c : K d₁ d₂) * sqrt_prod_K := by
  refine ⟨(sqrt_prod_K_basis hd12).repr x 0, (sqrt_prod_K_basis hd12).repr x 1, ?_⟩
  have h := (sqrt_prod_K_basis hd12).sum_repr x
  rw [Fin.sum_univ_two] at h
  have hc := congrArg
    (fun y : IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂)) => (y : K d₁ d₂)) h.symm
  simpa [sqrt_prod_K_basis, coe_basisOfLinearIndependentOfCardEqFinrank,
    AdjoinSimple.coe_gen, Algebra.smul_def] using hc

theorem phantom_middle_fixed_iff (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) (x : K d₁ d₂) :
    phantom_middle hd1 hd2 hd12 x = x ↔
      ∃ a b : ℚ, (x : ℝ) = (a : ℝ) + (b : ℝ) * (Real.sqrt (d₁ : ℝ) * Real.sqrt (d₂ : ℝ)) := by
  rw [← mem_fixedField_zpowers_phantom_iff hd1 hd2 hd12, fixedField_phantom_middle hd1 hd2 hd12]
  constructor
  · intro hx
    obtain ⟨a, c, hac⟩ := sqrt_prod_K_field_eq hd12
      (⟨x, hx⟩ : IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂)))
    refine ⟨a, c, ?_⟩
    have h := congrArg (fun y : K d₁ d₂ => (y : ℝ)) hac
    push_cast [sqrt_prod_K_coe] at h
    linarith [h]
  · rintro ⟨a, b, hab⟩
    have hmem : (a : K d₁ d₂) + (b : K d₁ d₂) * sqrt_prod_K
        ∈ IntermediateField.adjoin ℚ ({(sqrt_prod_K : K d₁ d₂)} : Set (K d₁ d₂)) :=
      add_mem (IntermediateField.algebraMap_mem _ a)
        (mul_mem (IntermediateField.algebraMap_mem _ b)
          (IntermediateField.mem_adjoin_simple_self ℚ (sqrt_prod_K : K d₁ d₂)))
    have hxeq : x = (a : K d₁ d₂) + (b : K d₁ d₂) * sqrt_prod_K := by
      apply Subtype.ext
      show (x : ℝ) = (((a : K d₁ d₂) + (b : K d₁ d₂) * sqrt_prod_K : K d₁ d₂) : ℝ)
      push_cast [sqrt_prod_K_coe]
      linarith [hab]
    rw [hxeq]
    exact hmem

/-! ## Sanity check: specializes to the `(2,3)` instance -/

/-- Reruns `PhantomFixedField.lean`'s own `stabilizer_sqrt6K` through this
file's general theorem, at `K` instantiated to `(2,3)`. The two `sqrt6K`s
(theirs, concrete; `sqrt_prod_K` here, at `d₁:=2,d₂:=3`) denote the same real
number `√2·√3`, so this checks the general stabilizer characterization
against the one PhantomFixedField.lean proved directly. -/
theorem stabilizer_sqrt_prod_at_2_3 (g : _root_.K ≃ₐ[ℚ] _root_.K) :
    g (sqrt_prod_K (d₁ := 2) (d₂ := 3)) = sqrt_prod_K (d₁ := 2) (d₂ := 3) ↔
      g = 1 ∨ g = phantom_middle
        (not_isSquare_of_not_exists_sq two_not_square)
        (not_isSquare_of_not_exists_sq three_not_square)
        (not_isSquare_of_not_exists_sq six_not_square) :=
  stabilizer_sqrt_prod
    (not_isSquare_of_not_exists_sq two_not_square)
    (not_isSquare_of_not_exists_sq three_not_square)
    (not_isSquare_of_not_exists_sq six_not_square) g

/-- The general fixed field, instantiated at `(2,3)`, is `ℚ⟮√2·√3⟯` — the same
conclusion as `PhantomFixedField.lean`'s `fixedField_phantom_middle`. -/
theorem fixedField_phantom_middle_at_2_3 :
    IntermediateField.fixedField (Subgroup.zpowers (phantom_middle
        (not_isSquare_of_not_exists_sq two_not_square)
        (not_isSquare_of_not_exists_sq three_not_square)
        (not_isSquare_of_not_exists_sq six_not_square))) =
      IntermediateField.adjoin ℚ ({(sqrt_prod_K (d₁ := 2) (d₂ := 3) : _root_.K)} : Set _root_.K) :=
  fixedField_phantom_middle
    (not_isSquare_of_not_exists_sq two_not_square)
    (not_isSquare_of_not_exists_sq three_not_square)
    (not_isSquare_of_not_exists_sq six_not_square)

end Theta0Photon.GeneralPhantomFixedField

end

#print axioms Theta0Photon.GeneralPhantomFixedField.stabilizer_sqrt_prod
#print axioms Theta0Photon.GeneralPhantomFixedField.fixedField_phantom_middle
#print axioms Theta0Photon.GeneralPhantomFixedField.phantom_middle_fixed_iff
#print axioms Theta0Photon.GeneralPhantomFixedField.stabilizer_sqrt_prod_at_2_3
#print axioms Theta0Photon.GeneralPhantomFixedField.fixedField_phantom_middle_at_2_3
