import Theta0Photon.Algebra.GeneralFieldTower
import Theta0Photon.Algebra.GaloisGroup
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# General Galois Group: `Gal(ℚ(√d₁,√d₂)/ℚ) ≅ V₄` for any independent pair

`GaloisGroup.lean` builds `Gal(K d₁ d₂/ℚ) ≅ V₄` and the Phantom Middle element for
the fixed pair `K d₁ d₂ = ℚ(√2,√3)`. This file reruns that construction — same
shape, same safety discipline around the `AlgEquiv.refl` auto-closing pitfall
documented in `GaloisGroup.lean`'s module doc — for an arbitrary pair
`d₁ d₂ : ℕ` satisfying the independence condition:

* `¬ IsSquare d₁`
* `¬ IsSquare d₂`
* `¬ IsSquare (d₁ * d₂)`

built on `GeneralFieldTower.lean`'s already-general tower (`sqrt_isIntegral_over`,
`X_sq_sub_irreducible_over`, `sqrt_minpoly_over`, `sqrt_sqrt_finrank`) instead
of `FieldTower.lean`'s `(2,3)`-specific §3.

**Two deliberate differences from `GaloisGroup.lean`, both noted so the
claims below stay exact:**

1. **`σ`'s construction needs one extra step `GaloisGroup.lean` didn't.**
   There, `σ` (flip `√2`, fix `√3`) was built over the base `ℚ⟮√3⟯` by
   mirroring the `τ` construction with the roles of `2,3` swapped, using a
   freshly-proved `sqrt2_notMem_sqrt3` (derived from `sqrt3_notMem` via a
   finrank/minimality argument, to avoid re-running the big case-split proof
   a second time). Here, `GeneralFieldTower.sqrt_notMem` is already fully
   symmetric in its two arguments, so the swapped fact `√d₁ ∉ ℚ⟮√d₂⟯` is just
   `sqrt_notMem` instantiated with its implicit arguments exchanged (and
   `¬IsSquare (d₂*d₁)` from `¬IsSquare (d₁*d₂)` via `mul_comm`) — no separate
   finrank detour needed, since the general lemma was already proved once for
   both orders.
2. **`IsGalois ℚ K d₁ d₂` and `IsKleinFour (K d₁ d₂ ≃ₐ[ℚ] K d₁ d₂)` are theorems here, not
   registered `instance`s.** `GaloisGroup.lean` can make them instances
   because `2` and `3` are concrete numerals with no hypotheses to discharge.
   Here `K d₁ d₂` depends on arbitrary `d₁, d₂` whose independence
   (`¬IsSquare d₁` etc.) Lean's instance search cannot conjure on its own —
   so these are named theorems taking those hypotheses explicitly, which is
   the only way to state them correctly for a free `(d₁,d₂)`.

No new mathematical content beyond `GaloisGroup.lean`'s own argument,
reparametrized: the `(2,3)` case is recovered exactly as a sanity check at
the end of this file.
-/

open Polynomial IntermediateField
open Theta0Photon.GeneralFieldTower

noncomputable section

namespace Theta0Photon.GeneralGaloisGroup

variable {d₁ d₂ : ℕ}

/-- `K d₁ d₂ = ℚ(√d₁, √d₂)`, with `d₁, d₂` **explicit** (unlike `GaloisGroup.lean`'s
concrete, zero-argument `K d₁ d₂`): since `d₁, d₂` don't appear in `K d₁ d₂`'s own result
type `IntermediateField ℚ ℝ`, Lean can't recover them from a bare type
ascription if they were implicit, so every use below writes `K d₁ d₂` out. -/
abbrev K (d₁ d₂ : ℕ) : IntermediateField ℚ ℝ := ℚ⟮Real.sqrt (d₁ : ℝ), Real.sqrt (d₂ : ℝ)⟯

noncomputable instance : DecidableEq (K d₁ d₂ ≃ₐ[ℚ] K d₁ d₂) := Classical.decEq _

theorem sqrt_d1_mem_K : Real.sqrt (d₁ : ℝ) ∈ (K d₁ d₂ : IntermediateField ℚ ℝ) :=
  subset_adjoin ℚ _ (Or.inl rfl)

theorem sqrt_d2_mem_K : Real.sqrt (d₂ : ℝ) ∈ (K d₁ d₂ : IntermediateField ℚ ℝ) :=
  subset_adjoin ℚ _ (Or.inr rfl)

instance : FiniteDimensional ℚ (K d₁ d₂ : IntermediateField ℚ ℝ) :=
  IntermediateField.finiteDimensional_adjoin
    (S := ({Real.sqrt (d₁ : ℝ), Real.sqrt (d₂ : ℝ)} : Set ℝ))
    (fun x hx => by rcases hx with h | h <;> subst h <;>
      [exact sqrt_isIntegral d₁; exact sqrt_isIntegral d₂])

/-- `¬ IsSquare (d₂ * d₁)` from `¬ IsSquare (d₁ * d₂)` — needed to build `σ`
over the swapped base `ℚ⟮√d₂⟯`. -/
theorem isSquare_swap (hd12 : ¬ IsSquare (d₁ * d₂)) : ¬ IsSquare (d₂ * d₁) := by
  rwa [mul_comm]

/-! ## §2 — Building τ (fix √d₁, flip √d₂) -/

/-- τ: the automorphism of `ℚ⟮√d₁⟯⟮√d₂⟯` over base `ℚ⟮√d₁⟯` sending `√d₂ ↦ -√d₂`. -/
def tau_hom (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ →ₐ[ℚ⟮Real.sqrt (d₁ : ℝ)⟯]
      ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ :=
  (algHomAdjoinIntegralEquiv ℚ⟮Real.sqrt (d₁ : ℝ)⟯
    (K := ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯) sqrt_isIntegral_over).symm
    ⟨-AdjoinSimple.gen ℚ⟮Real.sqrt (d₁ : ℝ)⟯ (Real.sqrt d₂), by
      rw [mem_aroots]
      refine ⟨?_, ?_⟩
      · rw [← sqrt_minpoly_over hd1 hd2 hd12]
        exact (X_sq_sub_irreducible_over hd1 hd2 hd12).ne_zero
      · rw [← sqrt_minpoly_over hd1 hd2 hd12]
        simp only [map_sub, map_pow, aeval_X, aeval_C, neg_sq]
        apply_fun (fun y : ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ => (y : ℝ))
          using Subtype.coe_injective
        push_cast [AdjoinSimple.coe_gen]
        norm_num [map_natCast, Real.sq_sqrt (Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂)]⟩

instance : FiniteDimensional ℚ⟮Real.sqrt (d₁ : ℝ)⟯ ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ :=
  IntermediateField.adjoin.finiteDimensional sqrt_isIntegral_over

def tau_equiv_base (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ ≃ₐ[ℚ⟮Real.sqrt (d₁ : ℝ)⟯]
      ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ :=
  AlgEquiv.ofBijective (tau_hom hd1 hd2 hd12) (AlgHom.bijective (tau_hom hd1 hd2 hd12))

/-- τ, transported into an automorphism of `K d₁ d₂` itself. -/
def tau_K (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂ :=
  (IntermediateField.equivOfEq (sqrt_sqrt_tower_eq (d₁ := d₁) (d₂ := d₂))).symm.trans
    (((tau_equiv_base hd1 hd2 hd12).restrictScalars ℚ).trans
      (IntermediateField.equivOfEq (sqrt_sqrt_tower_eq (d₁ := d₁) (d₂ := d₂))))

theorem tau_flips_sqrt_d2 (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : ℝ) = -Real.sqrt (d₂ : ℝ) := by
  simp only [tau_K, IntermediateField.equivOfEq_symm]
  show (tau_hom hd1 hd2 hd12
    (AdjoinSimple.gen ℚ⟮Real.sqrt (d₁ : ℝ)⟯ (Real.sqrt (d₂ : ℝ))) : ℝ) = -Real.sqrt (d₂ : ℝ)
  rw [tau_hom, algHomAdjoinIntegralEquiv_symm_apply_gen]
  simp [AdjoinSimple.coe_gen]

theorem tau_fixes_sqrt_d1 (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : ℝ) = Real.sqrt (d₁ : ℝ) := by
  simp only [tau_K, IntermediateField.equivOfEq_symm]
  show (tau_hom hd1 hd2 hd12 (algebraMap ℚ⟮Real.sqrt (d₁ : ℝ)⟯
      ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯
      (AdjoinSimple.gen ℚ (Real.sqrt (d₁ : ℝ)))) : ℝ) = Real.sqrt (d₁ : ℝ)
  rw [AlgHom.commutes]
  simp [AdjoinSimple.coe_gen]

/-! ## §3 — Building σ (flip √d₁, fix √d₂): roles of `d₁, d₂` exchanged -/

def sigma_hom (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯ →ₐ[ℚ⟮Real.sqrt (d₂ : ℝ)⟯]
      ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯ :=
  (algHomAdjoinIntegralEquiv ℚ⟮Real.sqrt (d₂ : ℝ)⟯
    (K := ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯) sqrt_isIntegral_over).symm
    ⟨-AdjoinSimple.gen ℚ⟮Real.sqrt (d₂ : ℝ)⟯ (Real.sqrt d₁), by
      rw [mem_aroots]
      refine ⟨?_, ?_⟩
      · rw [← sqrt_minpoly_over hd2 hd1 (isSquare_swap hd12)]
        exact (X_sq_sub_irreducible_over hd2 hd1 (isSquare_swap hd12)).ne_zero
      · rw [← sqrt_minpoly_over hd2 hd1 (isSquare_swap hd12)]
        simp only [map_sub, map_pow, aeval_X, aeval_C, neg_sq]
        apply_fun (fun y : ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯ => (y : ℝ))
          using Subtype.coe_injective
        push_cast [AdjoinSimple.coe_gen]
        norm_num [map_natCast, Real.sq_sqrt (Nat.cast_nonneg d₁ : (0:ℝ) ≤ d₁)]⟩

instance : FiniteDimensional ℚ⟮Real.sqrt (d₂ : ℝ)⟯ ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯ :=
  IntermediateField.adjoin.finiteDimensional sqrt_isIntegral_over

def sigma_equiv_base (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯ ≃ₐ[ℚ⟮Real.sqrt (d₂ : ℝ)⟯]
      ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯ :=
  AlgEquiv.ofBijective (sigma_hom hd1 hd2 hd12) (AlgHom.bijective (sigma_hom hd1 hd2 hd12))

/-- `ℚ⟮√d₂,√d₁⟯ = ℚ⟮√d₁,√d₂⟯ = K d₁ d₂`: `adjoin` only depends on the *set* of
generators. -/
theorem sqrt_d2_sqrt_d1_eq_K :
    (ℚ⟮Real.sqrt (d₂ : ℝ), Real.sqrt (d₁ : ℝ)⟯ : IntermediateField ℚ ℝ) = K d₁ d₂ :=
  congrArg (IntermediateField.adjoin ℚ) (Set.pair_comm (Real.sqrt (d₂ : ℝ)) (Real.sqrt (d₁ : ℝ)))

/-- σ, transported into an automorphism of `K d₁ d₂` itself. -/
def sigma_K (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂ :=
  (IntermediateField.equivOfEq
      ((sqrt_sqrt_tower_eq (d₁ := d₂) (d₂ := d₁)).trans sqrt_d2_sqrt_d1_eq_K)).symm.trans
    (((sigma_equiv_base hd1 hd2 hd12).restrictScalars ℚ).trans
      (IntermediateField.equivOfEq
        ((sqrt_sqrt_tower_eq (d₁ := d₂) (d₂ := d₁)).trans sqrt_d2_sqrt_d1_eq_K)))

theorem sigma_flips_sqrt_d1 (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : ℝ) = -Real.sqrt (d₁ : ℝ) := by
  simp only [sigma_K, IntermediateField.equivOfEq_symm]
  show (sigma_hom hd1 hd2 hd12
    (AdjoinSimple.gen ℚ⟮Real.sqrt (d₂ : ℝ)⟯ (Real.sqrt (d₁ : ℝ))) : ℝ) = -Real.sqrt (d₁ : ℝ)
  rw [sigma_hom, algHomAdjoinIntegralEquiv_symm_apply_gen]
  simp [AdjoinSimple.coe_gen]

theorem sigma_fixes_sqrt_d2 (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : ℝ) = Real.sqrt (d₂ : ℝ) := by
  simp only [sigma_K, IntermediateField.equivOfEq_symm]
  show (sigma_hom hd1 hd2 hd12 (algebraMap ℚ⟮Real.sqrt (d₂ : ℝ)⟯
      ℚ⟮Real.sqrt (d₂ : ℝ)⟯⟮Real.sqrt (d₁ : ℝ)⟯
      (AdjoinSimple.gen ℚ (Real.sqrt (d₂ : ℝ)))) : ℝ) = Real.sqrt (d₂ : ℝ)
  rw [AlgHom.commutes]
  simp [AdjoinSimple.coe_gen]

/-! ## Assembling the Klein four-group structure -/

/-- The "Phantom Middle" element: `σ` then `τ`, flipping **both** generators
simultaneously. -/
def phantom_middle (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂ :=
  (sigma_K hd1 hd2 hd12).trans (tau_K hd1 hd2 hd12)

theorem phantom_middle_sqrt_d1 (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (phantom_middle hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : ℝ) = -Real.sqrt (d₁ : ℝ) := by
  show (tau_K hd1 hd2 hd12 (sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩) : ℝ)
      = -Real.sqrt (d₁ : ℝ)
  have hset : sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩
      = (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (sigma_flips_sqrt_d1 hd1 hd2 hd12)
  rw [hset]
  show (tau_K hd1 hd2 hd12 ⟨-Real.sqrt (d₁ : ℝ), _⟩ : ℝ) = -Real.sqrt (d₁ : ℝ)
  have hneg : tau_K hd1 hd2 hd12 (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂)
      = -tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ := by
    have : (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂)
        = -(⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) := rfl
    rw [this, map_neg]
  rw [hneg]
  simp [tau_fixes_sqrt_d1 hd1 hd2 hd12]

theorem phantom_middle_sqrt_d2 (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    (phantom_middle hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : ℝ) = -Real.sqrt (d₂ : ℝ) := by
  show (tau_K hd1 hd2 hd12 (sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩) : ℝ)
      = -Real.sqrt (d₂ : ℝ)
  have hset : sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩
      = (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂) :=
    Subtype.ext (sigma_fixes_sqrt_d2 hd1 hd2 hd12)
  rw [hset]
  exact tau_flips_sqrt_d2 hd1 hd2 hd12

theorem one_sqrt_d1 :
    ((1 : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : ℝ)
      = Real.sqrt (d₁ : ℝ) := rfl

theorem one_sqrt_d2 :
    ((1 : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : ℝ)
      = Real.sqrt (d₂ : ℝ) := rfl

theorem sqrt_d1_pos (hd1 : ¬ IsSquare d₁) : (0:ℝ) < Real.sqrt (d₁ : ℝ) := by
  apply Real.sqrt_pos.mpr
  have : d₁ ≠ 0 := by
    rintro rfl
    exact hd1 ⟨0, rfl⟩
  exact_mod_cast Nat.pos_of_ne_zero this

theorem sqrt_d2_pos (hd2 : ¬ IsSquare d₂) : (0:ℝ) < Real.sqrt (d₂ : ℝ) := by
  apply Real.sqrt_pos.mpr
  have : d₂ ≠ 0 := by
    rintro rfl
    exact hd2 ⟨0, rfl⟩
  exact_mod_cast Nat.pos_of_ne_zero this

theorem sqrt_d1_ne_neg (hd1 : ¬ IsSquare d₁) : Real.sqrt (d₁ : ℝ) ≠ -Real.sqrt (d₁ : ℝ) := by
  have h := sqrt_d1_pos hd1
  intro heq; rw [heq] at h; linarith

theorem sqrt_d2_ne_neg (hd2 : ¬ IsSquare d₂) : Real.sqrt (d₂ : ℝ) ≠ -Real.sqrt (d₂ : ℝ) := by
  have h := sqrt_d2_pos hd2
  intro heq; rw [heq] at h; linarith

theorem ne_of_sqrt_d1_ne {φ ψ : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂}
    (h : (φ ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : ℝ) ≠ (ψ ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : ℝ)) :
    φ ≠ ψ := fun heq => h (by rw [heq])

theorem ne_of_sqrt_d2_ne {φ ψ : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂}
    (h : (φ ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : ℝ) ≠ (ψ ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : ℝ)) :
    φ ≠ ψ := fun heq => h (by rw [heq])

variable (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂))

theorem one_ne_sigma : (1 : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ≠ sigma_K hd1 hd2 hd12 :=
  ne_of_sqrt_d1_ne (by rw [one_sqrt_d1, sigma_flips_sqrt_d1 hd1 hd2 hd12]; exact sqrt_d1_ne_neg hd1)

theorem one_ne_tau : (1 : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ≠ tau_K hd1 hd2 hd12 :=
  ne_of_sqrt_d2_ne (by rw [one_sqrt_d2, tau_flips_sqrt_d2 hd1 hd2 hd12]; exact sqrt_d2_ne_neg hd2)

theorem one_ne_phantom : (1 : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ≠ phantom_middle hd1 hd2 hd12 :=
  ne_of_sqrt_d1_ne
    (by rw [one_sqrt_d1, phantom_middle_sqrt_d1 hd1 hd2 hd12]; exact sqrt_d1_ne_neg hd1)

theorem sigma_ne_tau : sigma_K hd1 hd2 hd12 ≠ tau_K hd1 hd2 hd12 :=
  ne_of_sqrt_d1_ne (by
    rw [sigma_flips_sqrt_d1 hd1 hd2 hd12, tau_fixes_sqrt_d1 hd1 hd2 hd12]
    exact (sqrt_d1_ne_neg hd1).symm)

theorem sigma_ne_phantom : sigma_K hd1 hd2 hd12 ≠ phantom_middle hd1 hd2 hd12 :=
  ne_of_sqrt_d2_ne (by
    rw [sigma_fixes_sqrt_d2 hd1 hd2 hd12, phantom_middle_sqrt_d2 hd1 hd2 hd12]
    exact sqrt_d2_ne_neg hd2)

theorem tau_ne_phantom : tau_K hd1 hd2 hd12 ≠ phantom_middle hd1 hd2 hd12 :=
  ne_of_sqrt_d1_ne (by
    rw [tau_fixes_sqrt_d1 hd1 hd2 hd12, phantom_middle_sqrt_d1 hd1 hd2 hd12]
    exact sqrt_d1_ne_neg hd1)

/-- The four elements `{1, σ, τ, σ∘τ}` are pairwise distinct. -/
theorem four_elts_finset_card :
    ({1, sigma_K hd1 hd2 hd12, tau_K hd1 hd2 hd12, phantom_middle hd1 hd2 hd12} :
        Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)).card = 4 := by
  classical
  have h1 : (1 : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ∉
      ({sigma_K hd1 hd2 hd12, tau_K hd1 hd2 hd12, phantom_middle hd1 hd2 hd12} :
        Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)) := by
    simp [one_ne_sigma hd1 hd2 hd12, one_ne_tau hd1 hd2 hd12, one_ne_phantom hd1 hd2 hd12]
  have h2 : sigma_K hd1 hd2 hd12 ∉
      ({tau_K hd1 hd2 hd12, phantom_middle hd1 hd2 hd12} :
        Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)) := by
    simp [sigma_ne_tau hd1 hd2 hd12, sigma_ne_phantom hd1 hd2 hd12]
  have h3 : tau_K hd1 hd2 hd12 ∉
      ({phantom_middle hd1 hd2 hd12} : Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)) := by
    simp [tau_ne_phantom hd1 hd2 hd12]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton]

include hd1 hd2 hd12 in
theorem card_Gal_ge_four : 4 ≤ Fintype.card ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) :=
  four_elts_finset_card hd1 hd2 hd12 ▸ Finset.card_le_univ _

include hd1 hd2 hd12 in
/-- **Exactly 4 automorphisms.** The general-`(d₁,d₂)` form of `GaloisGroup`'s
`card_Gal_eq_four`. -/
theorem card_Gal_eq_four : Fintype.card ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) = 4 := by
  have hle : Fintype.card ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)
      ≤ Module.finrank ℚ (K d₁ d₂) :=
    AlgEquiv.card_le
  rw [sqrt_sqrt_finrank hd1 hd2 hd12] at hle
  exact le_antisymm hle (card_Gal_ge_four hd1 hd2 hd12)

include hd1 hd2 hd12 in
theorem nat_card_Gal_eq_four : Nat.card ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) = 4 := by
  rw [Nat.card_eq_fintype_card, card_Gal_eq_four hd1 hd2 hd12]

include hd1 hd2 hd12 in
/-- **`K d₁ d₂/ℚ` is Galois**, for any independent pair `(d₁,d₂)`. A theorem, not a
registered `instance` — see the module docstring for why. -/
theorem isGalois_K : IsGalois ℚ (K d₁ d₂ : IntermediateField ℚ ℝ) :=
  IsGalois.of_card_aut_eq_finrank ℚ (K d₁ d₂)
    ((nat_card_Gal_eq_four hd1 hd2 hd12).trans (sqrt_sqrt_finrank hd1 hd2 hd12).symm)

include hd1 hd2 hd12 in
theorem four_elts_eq_univ :
    ({1, sigma_K hd1 hd2 hd12, tau_K hd1 hd2 hd12, phantom_middle hd1 hd2 hd12} :
        Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)) = Finset.univ :=
  Finset.eq_univ_of_card _ ((four_elts_finset_card hd1 hd2 hd12).trans
    (card_Gal_eq_four hd1 hd2 hd12).symm)

/-- Two `ℚ`-automorphisms of `K d₁ d₂` agreeing on `√d₁` and `√d₂` are equal. -/
theorem algEquiv_ext_gens (φ ψ : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)
    (h1 : φ ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ = ψ ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩)
    (h2 : φ ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ = ψ ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩) :
    φ = ψ := by
  have hAlgHom : φ.toAlgHom = ψ.toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ
      (S := (K d₁ d₂ : IntermediateField ℚ ℝ)) (s := ({Real.sqrt (d₁ : ℝ), Real.sqrt (d₂ : ℝ)} : Set ℝ))
      rfl
    intro x hx
    rcases hx with h | h
    · subst h; exact h1
    · subst h; exact h2
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hAlgHom x)

/-! ## Every non-identity element has order 2 -/

theorem sigma_sq : sigma_K hd1 hd2 hd12 ^ 2 = 1 := by
  apply algEquiv_ext_gens
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (sigma_K hd1 hd2 hd12 (sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩) : ℝ)
        = Real.sqrt (d₁ : ℝ)
    have hset : sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩
        = (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂) :=
      Subtype.ext (sigma_flips_sqrt_d1 hd1 hd2 hd12)
    rw [hset]
    have hneg : (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂)
        = -(⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) := rfl
    simp [hneg, sigma_flips_sqrt_d1 hd1 hd2 hd12]
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (sigma_K hd1 hd2 hd12 (sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩) : ℝ)
        = Real.sqrt (d₂ : ℝ)
    have hset : sigma_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩
        = (⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂) :=
      Subtype.ext (sigma_fixes_sqrt_d2 hd1 hd2 hd12)
    rw [hset, sigma_fixes_sqrt_d2 hd1 hd2 hd12]

theorem tau_sq : tau_K hd1 hd2 hd12 ^ 2 = 1 := by
  apply algEquiv_ext_gens
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (tau_K hd1 hd2 hd12 (tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩) : ℝ)
        = Real.sqrt (d₁ : ℝ)
    have hset : tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩
        = (⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) :=
      Subtype.ext (tau_fixes_sqrt_d1 hd1 hd2 hd12)
    rw [hset, tau_fixes_sqrt_d1 hd1 hd2 hd12]
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (tau_K hd1 hd2 hd12 (tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩) : ℝ)
        = Real.sqrt (d₂ : ℝ)
    have hset : tau_K hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩
        = (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂) :=
      Subtype.ext (tau_flips_sqrt_d2 hd1 hd2 hd12)
    rw [hset]
    have hneg : (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂)
        = -(⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂) := rfl
    simp [hneg, tau_flips_sqrt_d2 hd1 hd2 hd12]

theorem phantom_sq : phantom_middle hd1 hd2 hd12 ^ 2 = 1 := by
  apply algEquiv_ext_gens
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (phantom_middle hd1 hd2 hd12
        (phantom_middle hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩) : ℝ)
        = Real.sqrt (d₁ : ℝ)
    have hset : phantom_middle hd1 hd2 hd12 ⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩
        = (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂) :=
      Subtype.ext (phantom_middle_sqrt_d1 hd1 hd2 hd12)
    rw [hset]
    have hneg : (⟨-Real.sqrt (d₁ : ℝ), by simpa using neg_mem sqrt_d1_mem_K⟩ : K d₁ d₂)
        = -(⟨Real.sqrt (d₁ : ℝ), sqrt_d1_mem_K⟩ : K d₁ d₂) := rfl
    simp [hneg, phantom_middle_sqrt_d1 hd1 hd2 hd12]
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (phantom_middle hd1 hd2 hd12
        (phantom_middle hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩) : ℝ)
        = Real.sqrt (d₂ : ℝ)
    have hset : phantom_middle hd1 hd2 hd12 ⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩
        = (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂) :=
      Subtype.ext (phantom_middle_sqrt_d2 hd1 hd2 hd12)
    rw [hset]
    have hneg : (⟨-Real.sqrt (d₂ : ℝ), by simpa using neg_mem sqrt_d2_mem_K⟩ : K d₁ d₂)
        = -(⟨Real.sqrt (d₂ : ℝ), sqrt_d2_mem_K⟩ : K d₁ d₂) := rfl
    simp [hneg, phantom_middle_sqrt_d2 hd1 hd2 hd12]

include hd1 hd2 hd12 in
theorem forall_sq_eq_one : ∀ g : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂, g ^ 2 = 1 := by
  intro g
  have hmem : g ∈ ({1, sigma_K hd1 hd2 hd12, tau_K hd1 hd2 hd12, phantom_middle hd1 hd2 hd12} :
      Finset ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂)) := by
    rw [four_elts_eq_univ hd1 hd2 hd12]; exact Finset.mem_univ g
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> subst h
  · exact one_pow 2
  · exact sigma_sq hd1 hd2 hd12
  · exact tau_sq hd1 hd2 hd12
  · exact phantom_sq hd1 hd2 hd12

include hd1 hd2 hd12 in
theorem exists_ne_one : ∃ g : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂, g ≠ 1 :=
  ⟨sigma_K hd1 hd2 hd12, (one_ne_sigma hd1 hd2 hd12).symm⟩

include hd1 hd2 hd12 in
theorem exponent_Gal_eq_two : Monoid.exponent ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) = 2 := by
  have hdvd : Monoid.exponent ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (forall_sq_eq_one hd1 hd2 hd12)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have hone : ∀ g : (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂, g ^ 1 = 1 := by
      have h := (Monoid.exponent_dvd_iff_forall_pow_eq_one
        (G := (K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) (n := 1))
      rw [h1] at h
      exact h.mp dvd_rfl
    obtain ⟨g, hg⟩ := exists_ne_one hd1 hd2 hd12
    exact hg (by simpa using hone g)
  · exact h2

include hd1 hd2 hd12 in
/-- **`Gal(K d₁ d₂/ℚ)` is a Klein four-group**, for any independent pair `(d₁,d₂)`.
A theorem, not a registered `instance` — see the module docstring for why. -/
theorem isKleinFour_K : IsKleinFour ((K d₁ d₂ : IntermediateField ℚ ℝ) ≃ₐ[ℚ] K d₁ d₂) where
  card_four := nat_card_Gal_eq_four hd1 hd2 hd12
  exponent_two := exponent_Gal_eq_two hd1 hd2 hd12

/-! ## Sanity check: specializes to the `(2,3)` instance -/

/-- Reruns `GaloisGroup.lean`'s own `card_Gal_eq_four` through this file's
general theorem, at the exact same type `_root_.K ≃ₐ[ℚ] _root_.K` — not just a
matching numeral, but the same automorphism group. -/
theorem card_Gal_eq_four_at_2_3 : Fintype.card (_root_.K ≃ₐ[ℚ] _root_.K) = 4 :=
  card_Gal_eq_four (d₁ := 2) (d₂ := 3)
    (not_isSquare_of_not_exists_sq two_not_square)
    (not_isSquare_of_not_exists_sq three_not_square)
    (not_isSquare_of_not_exists_sq six_not_square)

end Theta0Photon.GeneralGaloisGroup

end

#print axioms Theta0Photon.GeneralGaloisGroup.card_Gal_eq_four
#print axioms Theta0Photon.GeneralGaloisGroup.isGalois_K
#print axioms Theta0Photon.GeneralGaloisGroup.isKleinFour_K
#print axioms Theta0Photon.GeneralGaloisGroup.card_Gal_eq_four_at_2_3
