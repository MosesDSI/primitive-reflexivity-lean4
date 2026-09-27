import Theta0Photon.Algebra.GaloisGroup

/-!
# The Phantom Middle preserves exactly the product

In `K = ℚ(√2, √3)`, the Phantom Middle `π = σ ∘ τ` flips both `√2` and `√3`.
What `π` preserves is exactly the *product* of the two generators,
`√2 · √3 = √6`:

* **A.** `π` fixes `√2·√3`, while `σ` and `τ` each negate it (non-vacuity).
* **B.** Among all four automorphisms, exactly `1` and `π` fix `√2·√3`.
* **D.** (Galois form) The fixed field of `⟨π⟩` is `ℚ(√2·√3)`.
* **C.** An element of `K` is fixed by `π` iff it has the form `a + b·√2·√3`
  with `a, b ∈ ℚ`.
-/

open Polynomial IntermediateField

noncomputable section

namespace Theta0Photon.PhantomFixedField

/-! ## Setup -/

/-- `√2 · √3 ∈ K`. -/
theorem sqrt6_mem_K : Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ) ∈ K :=
  mul_mem sqrt2_mem_K sqrt3_mem_K

/-- The product of the two generators, `√2 · √3`, as an element of `K`. -/
def sqrt6K : K := ⟨Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ), sqrt6_mem_K⟩

/-- Bookkeeping: `sqrt6K`'s real value, exposed for `simp`/`push_cast`. -/
@[simp] theorem sqrt6K_coe : (sqrt6K : ℝ) = Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ) := rfl

/-- Bookkeeping: the product equals `√6` as a real number. -/
theorem sqrt2_mul_sqrt3 : Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ) = Real.sqrt 6 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) 3]
  norm_num

/-- `√2 · √3`, as a real number, is positive. -/
theorem sqrt6K_pos : (0:ℝ) < (sqrt6K : ℝ) :=
  mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- The product is not its own negative (it is nonzero). -/
theorem sqrt6K_ne_neg : sqrt6K ≠ -sqrt6K := by
  intro h
  have hcoe : (sqrt6K : ℝ) = -(sqrt6K : ℝ) := congrArg (fun y : K => (y : ℝ)) h
  linarith [sqrt6K_pos]

/-! ## A. The Phantom Middle fixes the product; each single flip negates it -/

/-- `sqrt6K` as the product of the two generators inside `K`. -/
theorem sqrt6K_eq_mul :
    sqrt6K = (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) * (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) :=
  rfl

/-- `sqrt6K * sqrt6K = (6 : K)`. -/
theorem sqrt6K_mul_self : sqrt6K * sqrt6K = (6 : K) := by
  apply Subtype.ext
  show Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ) * (Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ)) = ((6:K) : ℝ)
  have h6 : ((6:K) : ℝ) = (6:ℝ) := by norm_cast
  have h2 : Real.sqrt (2:ℝ) * Real.sqrt (2:ℝ) = 2 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num); rwa [sq] at this
  have h3 : Real.sqrt (3:ℝ) * Real.sqrt (3:ℝ) = 3 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num); rwa [sq] at this
  rw [h6]
  calc Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ) * (Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ))
      = Real.sqrt (2:ℝ) * Real.sqrt (2:ℝ) * (Real.sqrt (3:ℝ) * Real.sqrt (3:ℝ)) := by ring
    _ = 2 * 3 := by rw [h2, h3]
    _ = 6 := by norm_num

theorem phantom_middle_fixes_sqrt6K : phantom_middle sqrt6K = sqrt6K := by
  rw [sqrt6K_eq_mul, map_mul]
  have h2 : phantom_middle (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K)
      = (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K) :=
    Subtype.ext phantom_middle_sqrt2
  have h3 : phantom_middle (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K)
      = (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K) :=
    Subtype.ext phantom_middle_sqrt3
  rw [h2, h3]
  apply Subtype.ext
  show (-Real.sqrt (2:ℝ)) * (-Real.sqrt (3:ℝ)) = Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ)
  ring

theorem sigma_negates_sqrt6K : sigma_K sqrt6K = -sqrt6K := by
  rw [sqrt6K_eq_mul, map_mul]
  have h2 : sigma_K (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K)
      = (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K) :=
    Subtype.ext sigma_flips_sqrt2
  have h3 : sigma_K (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) = (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) :=
    Subtype.ext sigma_fixes_sqrt3
  rw [h2, h3]
  apply Subtype.ext
  show (-Real.sqrt (2:ℝ)) * Real.sqrt (3:ℝ) = -(Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ))
  ring

theorem tau_negates_sqrt6K : tau_K sqrt6K = -sqrt6K := by
  rw [sqrt6K_eq_mul, map_mul]
  have h2 : tau_K (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) = (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) :=
    Subtype.ext tau_fixes_sqrt2
  have h3 : tau_K (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K)
      = (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K) :=
    Subtype.ext tau_flips_sqrt3
  rw [h2, h3]
  apply Subtype.ext
  show Real.sqrt (2:ℝ) * (-Real.sqrt (3:ℝ)) = -(Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ))
  ring

/-! ## B. Exactly the identity and the Phantom Middle preserve the product -/

theorem stabilizer_sqrt6K (g : K ≃ₐ[ℚ] K) :
    g sqrt6K = sqrt6K ↔ g = 1 ∨ g = phantom_middle := by
  constructor
  · intro hg
    have hmem : g ∈ ({1, sigma_K, tau_K, phantom_middle} : Finset (K ≃ₐ[ℚ] K)) := by
      rw [four_elts_eq_univ]; exact Finset.mem_univ g
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exfalso; rw [h, sigma_negates_sqrt6K] at hg; exact sqrt6K_ne_neg hg.symm
    · exfalso; rw [h, tau_negates_sqrt6K] at hg; exact sqrt6K_ne_neg hg.symm
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]; rfl
    · rw [h]; exact phantom_middle_fixes_sqrt6K

/-! ## D. Galois form: the fixed field of the Phantom Middle is `ℚ(√2·√3)` -/

/-- `phantom_middle` fixes `x` iff `x` is fixed by every element of the
subgroup it generates — the cyclic subgroup's fixed points reduce to a
single equation, via the stabilizer of `x` under the natural action. -/
theorem mem_fixedField_zpowers_phantom_iff (x : K) :
    x ∈ IntermediateField.fixedField (Subgroup.zpowers phantom_middle) ↔
      phantom_middle x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h phantom_middle (Subgroup.mem_zpowers phantom_middle)
  · intro h f hf
    have hmem : phantom_middle ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h
    have := (Subgroup.zpowers_le.mpr hmem) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this

/-- `phantom_middle` has order exactly `2` in `Gal(K/ℚ)`. -/
theorem orderOf_phantom_middle : orderOf phantom_middle = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime phantom_sq (Ne.symm one_ne_phantom)

/-- The cyclic subgroup generated by `phantom_middle` has exactly `2` elements. -/
theorem card_zpowers_phantom_middle : Nat.card (Subgroup.zpowers phantom_middle) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, orderOf_phantom_middle]

/-- `sqrt6K` is integral over `ℚ`, via the monic witness `X² - 6`. -/
theorem sqrt6K_isIntegral : IsIntegral ℚ sqrt6K := by
  refine ⟨X ^ 2 - C (6 : ℚ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_ofNat, sq, sqrt6K_mul_self, sub_self]

/-- `X² - 6` **is** `minpoly ℚ sqrt6K`, using the ground irreducibility fact
directly (it is a statement about `ℚ[X]`, independent of which field the
root lives in). -/
theorem sqrt6K_minpoly : X ^ 2 - C (6 : ℚ) = minpoly ℚ sqrt6K := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact triadic_ground_irreducible 6 six_not_square
  · rw [map_sub, map_pow, aeval_X, aeval_C, map_ofNat, sq, sqrt6K_mul_self, sub_self]
  · exact monic_X_pow_sub_C _ two_ne_zero

/-- `[ℚ⟮sqrt6K⟯ : ℚ] = 2`, computed exactly as `sqrt_finrank` is, but for the
`K`-internal generator `sqrt6K` rather than a real-number generator. -/
theorem sqrt6K_finrank :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({sqrt6K} : Set K)) = 2 := by
  rw [IntermediateField.adjoin.finrank sqrt6K_isIntegral, ← sqrt6K_minpoly, natDegree_X_pow_sub_C]

theorem fixedField_phantom_middle :
    IntermediateField.fixedField (Subgroup.zpowers phantom_middle) =
      IntermediateField.adjoin ℚ ({sqrt6K} : Set K) := by
  have hle : (IntermediateField.adjoin ℚ ({sqrt6K} : Set K)) ≤
      IntermediateField.fixedField (Subgroup.zpowers phantom_middle) :=
    IntermediateField.adjoin_simple_le_iff.mpr
      ((mem_fixedField_zpowers_phantom_iff sqrt6K).mpr phantom_middle_fixes_sqrt6K)
  have htower := Module.finrank_mul_finrank ℚ
    (IntermediateField.fixedField (Subgroup.zpowers phantom_middle)) K
  rw [IntermediateField.finrank_fixedField_eq_card, card_zpowers_phantom_middle,
    sqrt2_sqrt3_finrank] at htower
  have hfinrank : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers phantom_middle))
      = 2 := by omega
  exact (IntermediateField.eq_of_le_of_finrank_eq hle (sqrt6K_finrank.trans hfinrank.symm)).symm

/-! ## C. Elementwise form: the fixed elements are exactly `a + b·√2·√3` -/

/-- `{1, sqrt6K}` is `ℚ`-linearly independent in `ℚ⟮sqrt6K⟯`. -/
theorem sqrt6K_basis_indep :
    LinearIndependent ℚ
      (![1, AdjoinSimple.gen ℚ sqrt6K] :
        Fin 2 → IntermediateField.adjoin ℚ ({sqrt6K} : Set K)) := by
  rw [LinearIndependent.pair_iff' one_ne_zero]
  intro a ha
  have hK : (a : K) = sqrt6K := by
    have h := congrArg (fun y : IntermediateField.adjoin ℚ ({sqrt6K} : Set K) => (y : K)) ha
    simpa [Algebra.smul_def, AdjoinSimple.coe_gen] using h
  have hR : (a : ℝ) = Real.sqrt 6 := by
    have h := congrArg (fun y : K => (y : ℝ)) hK
    simpa [sqrt2_mul_sqrt3] using h
  exact sqrt_ne_ratCast 6 six_not_square a hR

/-- The resulting basis `{1, sqrt6K}` of `ℚ⟮sqrt6K⟯` over `ℚ`. -/
def sqrt6K_basis :
    Module.Basis (Fin 2) ℚ (IntermediateField.adjoin ℚ ({sqrt6K} : Set K)) :=
  basisOfLinearIndependentOfCardEqFinrank sqrt6K_basis_indep (by simp [sqrt6K_finrank])

/-- Every element of `ℚ⟮sqrt6K⟯` has the form `a + c·sqrt6K` for rationals `a, c`. -/
theorem sqrt6K_field_eq (x : IntermediateField.adjoin ℚ ({sqrt6K} : Set K)) :
    ∃ a c : ℚ, (x : K) = (a : K) + (c : K) * sqrt6K := by
  refine ⟨sqrt6K_basis.repr x 0, sqrt6K_basis.repr x 1, ?_⟩
  have h := sqrt6K_basis.sum_repr x
  rw [Fin.sum_univ_two] at h
  have hc := congrArg (fun y : IntermediateField.adjoin ℚ ({sqrt6K} : Set K) => (y : K)) h.symm
  simpa [sqrt6K_basis, coe_basisOfLinearIndependentOfCardEqFinrank,
    AdjoinSimple.coe_gen, Algebra.smul_def] using hc

theorem phantom_middle_fixed_iff (x : K) :
    phantom_middle x = x ↔
      ∃ a b : ℚ, (x : ℝ) = (a : ℝ) + (b : ℝ) * (Real.sqrt (2:ℝ) * Real.sqrt (3:ℝ)) := by
  rw [← mem_fixedField_zpowers_phantom_iff, fixedField_phantom_middle]
  constructor
  · intro hx
    obtain ⟨a, c, hac⟩ := sqrt6K_field_eq (⟨x, hx⟩ : IntermediateField.adjoin ℚ ({sqrt6K} : Set K))
    refine ⟨a, c, ?_⟩
    have h := congrArg (fun y : K => (y : ℝ)) hac
    push_cast [sqrt6K_coe] at h
    linarith [h]
  · rintro ⟨a, b, hab⟩
    have hmem : (a : K) + (b : K) * sqrt6K ∈ IntermediateField.adjoin ℚ ({sqrt6K} : Set K) :=
      add_mem (IntermediateField.algebraMap_mem _ a)
        (mul_mem (IntermediateField.algebraMap_mem _ b)
          (IntermediateField.mem_adjoin_simple_self ℚ sqrt6K))
    have hxeq : x = (a : K) + (b : K) * sqrt6K := by
      apply Subtype.ext
      show (x : ℝ) = (((a : K) + (b : K) * sqrt6K : K) : ℝ)
      push_cast [sqrt6K_coe]
      linarith [hab]
    rw [hxeq]
    exact hmem

end Theta0Photon.PhantomFixedField

#print axioms Theta0Photon.PhantomFixedField.sqrt2_mul_sqrt3
#print axioms Theta0Photon.PhantomFixedField.sqrt6K_ne_neg
#print axioms Theta0Photon.PhantomFixedField.phantom_middle_fixes_sqrt6K
#print axioms Theta0Photon.PhantomFixedField.sigma_negates_sqrt6K
#print axioms Theta0Photon.PhantomFixedField.tau_negates_sqrt6K
#print axioms Theta0Photon.PhantomFixedField.stabilizer_sqrt6K
#print axioms Theta0Photon.PhantomFixedField.fixedField_phantom_middle
#print axioms Theta0Photon.PhantomFixedField.phantom_middle_fixed_iff
