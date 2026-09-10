import Theta0Photon.Algebra.FieldTower
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The Galois Group of `K = ℚ(√2, √3)`: `Gal(K/ℚ) ≅ V₄`, and the Phantom Middle

Builds on `FieldTower.lean`'s closed degree-4 tower (`[K:ℚ] = 4`) to establish
the requested four-step result in full:

1. **`IsGalois ℚ K`** — not via constructing a splitting field directly, but
   via the converse criterion `IsGalois.of_card_aut_eq_finrank`: exhibit four
   pairwise-distinct automorphisms (§2–3 below), giving `Nat.card Gal(K/ℚ) ≥ 4`;
   combined with the general upper bound `AlgEquiv.card_le` (`≤ [K:ℚ] = 4`),
   this pins `Nat.card Gal(K/ℚ) = [K:ℚ]` exactly, which *is* Galois-ness.
2. **The explicit sign-flip `AlgEquiv`s** `σ` (flips `√2`, fixes `√3`) and `τ`
   (fixes `√2`, flips `√3`), each built by re-running `FieldTower.lean`'s
   `algHomAdjoinIntegralEquiv`-based construction one field up, then upgraded
   to bijections via `AlgHom.bijective` (finite-dimensional endomorphisms of a
   field are automatically bijective once injective).
3. **`Monoid.exponent Gal(K/ℚ) = 2`** — the four elements `{1, σ, τ, σ∘τ}`
   already exhaust the group (by the cardinality result), and each was
   checked individually to square to `1`.
4. **`IsKleinFour Gal(K/ℚ)`**, and the explicit isomorphism
   `Gal(K/ℚ) ≃* Multiplicative (ZMod 2 × ZMod 2)` — via Mathlib's
   `IsKleinFour.mulEquiv`, built from a bijection chosen so that `σ∘τ` — the
   "Phantom Middle" element, flipping *both* generators simultaneously —
   lands exactly on `Multiplicative (1,1)`, verified explicitly in
   `galoisKleinFourEquiv_phantom_middle`.

**A safety note that materially shaped this file's proof style:** an early
attempt to transport `τ` across a `restrictScalars` type-identification via
plain tactics (`rw`/`show` on a goal of the literal shape `X ≃ₐ[R] X`) was
silently auto-closed by `AlgEquiv.refl` — Lean's `rw`/`rfl` machinery treats
`@[refl]`-tagged relations like `AlgEquiv` as trivially provable once both
sides are syntactically identical, which would have made `τ` secretly the
*identity* rather than the intended flip, with no error raised. Caught only
by adding explicit numeric sanity checks (`tau_flips_sqrt3`,
`tau_fixes_sqrt2`, and their `σ` analogues) verifying the constructed
automorphisms act on `√2`/`√3` as claimed, *before* trusting them for
anything downstream — every such construction below is independently checked
this way, and the transport itself was rebuilt using `IntermediateField.equivOfEq`
(term-mode, no tactic-triggered auto-refl risk) once the danger was found.
-/

open Polynomial IntermediateField

noncomputable section

abbrev K := ℚ⟮Real.sqrt (2:ℝ), Real.sqrt (3:ℝ)⟯

noncomputable instance : DecidableEq (K ≃ₐ[ℚ] K) := Classical.decEq _

/-- `√2 ∈ K` and `√3 ∈ K`, needed constantly below. -/
theorem sqrt2_mem_K : Real.sqrt (2:ℝ) ∈ K :=
  subset_adjoin ℚ _ (Or.inl rfl)

theorem sqrt3_mem_K : Real.sqrt (3:ℝ) ∈ K :=
  subset_adjoin ℚ _ (Or.inr rfl)

instance : FiniteDimensional ℚ K :=
  IntermediateField.finiteDimensional_adjoin
    (S := ({Real.sqrt (2:ℝ), Real.sqrt (3:ℝ)} : Set ℝ))
    (fun x hx => by rcases hx with h | h <;> subst h <;>
      [exact sqrt_isIntegral 2; exact sqrt_isIntegral 3])

/-! ## §2 — Building τ (fix √2, flip √3), reusing `FieldTower.lean`'s §3 -/

/-- τ: the automorphism of `ℚ⟮√2⟯⟮√3⟯` over base `ℚ⟮√2⟯` sending `√3 ↦ -√3`. -/
def tau_hom : ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ →ₐ[ℚ⟮Real.sqrt (2:ℝ)⟯]
    ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ :=
  (algHomAdjoinIntegralEquiv ℚ⟮Real.sqrt (2:ℝ)⟯
    (K := ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯) sqrt3_isIntegral_over_sqrt2).symm
    ⟨-AdjoinSimple.gen ℚ⟮Real.sqrt (2:ℝ)⟯ (Real.sqrt 3), by
      rw [mem_aroots]
      refine ⟨?_, ?_⟩
      · rw [← sqrt3_minpoly_over_sqrt2]
        exact X_sq_sub_three_irreducible_over_sqrt2.ne_zero
      · rw [← sqrt3_minpoly_over_sqrt2]
        simp only [map_sub, map_pow, aeval_X, aeval_C, neg_sq]
        apply_fun (fun y : ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ => (y:ℝ))
          using Subtype.coe_injective
        push_cast [AdjoinSimple.coe_gen]
        norm_num [map_ofNat, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]⟩

instance : FiniteDimensional ℚ⟮Real.sqrt (2:ℝ)⟯ ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ :=
  IntermediateField.adjoin.finiteDimensional sqrt3_isIntegral_over_sqrt2

/-- τ upgraded to an `AlgEquiv` (over `ℚ⟮√2⟯`), via finite-dimensional
injective-implies-bijective. -/
def tau_equiv_base : ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ ≃ₐ[ℚ⟮Real.sqrt (2:ℝ)⟯]
    ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ :=
  AlgEquiv.ofBijective tau_hom (AlgHom.bijective tau_hom)

/-- τ, viewed over `ℚ` (via `restrictScalars`), then transported along
`sqrt2_sqrt3_tower_eq` into an automorphism of `K` itself. -/
def tau_K : K ≃ₐ[ℚ] K :=
  (IntermediateField.equivOfEq sqrt2_sqrt3_tower_eq).symm.trans
    ((tau_equiv_base.restrictScalars ℚ).trans (IntermediateField.equivOfEq sqrt2_sqrt3_tower_eq))

-- Sanity check: confirm this is NOT the identity (i.e. genuinely flips √3) —
-- catching exactly the "rfl auto-closed to the identity" risk before trusting the construction.
theorem tau_flips_sqrt3 : (tau_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : ℝ) = -Real.sqrt (3:ℝ) := by
  simp only [tau_K, IntermediateField.equivOfEq_symm]
  show (tau_hom (AdjoinSimple.gen ℚ⟮Real.sqrt (2:ℝ)⟯ (Real.sqrt (3:ℝ))) : ℝ) = -Real.sqrt (3:ℝ)
  rw [tau_hom, algHomAdjoinIntegralEquiv_symm_apply_gen]
  simp [AdjoinSimple.coe_gen]

theorem tau_fixes_sqrt2 : (tau_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : ℝ) = Real.sqrt (2:ℝ) := by
  simp only [tau_K, IntermediateField.equivOfEq_symm]
  show (tau_hom (algebraMap ℚ⟮Real.sqrt (2:ℝ)⟯ ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯
      (AdjoinSimple.gen ℚ (Real.sqrt (2:ℝ)))) : ℝ) = Real.sqrt (2:ℝ)
  rw [AlgHom.commutes]
  simp [AdjoinSimple.coe_gen]

/-! ## §3 — Building σ (flip √2, fix √3): mirror §2 with the roles of 2, 3 swapped -/

/-- `√2 ∉ ℚ⟮√3⟯`, obtained as a corollary of `sqrt3_notMem` (not re-derived from
scratch): if `√2 ∈ ℚ⟮√3⟯`, then `ℚ⟮√2⟯ ≤ ℚ⟮√3⟯` (minimality of adjoin), and
since both have `finrank = 2` over `ℚ`, they're equal — so `√3 ∈ ℚ⟮√2⟯`,
contradicting `sqrt3_notMem` directly. -/
theorem sqrt2_notMem_sqrt3 : Real.sqrt (2:ℝ) ∉ (ℚ⟮Real.sqrt (3:ℝ)⟯ : IntermediateField ℚ ℝ) := by
  have : FiniteDimensional ℚ ℚ⟮Real.sqrt (3:ℝ)⟯ :=
    IntermediateField.adjoin.finiteDimensional (sqrt_isIntegral 3)
  intro hmem
  have hle : (ℚ⟮Real.sqrt (2:ℝ)⟯ : IntermediateField ℚ ℝ) ≤ ℚ⟮Real.sqrt (3:ℝ)⟯ :=
    (IntermediateField.adjoin_simple_le_iff).mpr hmem
  have heq : (ℚ⟮Real.sqrt (2:ℝ)⟯ : IntermediateField ℚ ℝ) = ℚ⟮Real.sqrt (3:ℝ)⟯ :=
    IntermediateField.eq_of_le_of_finrank_eq hle (sqrt2_finrank.trans sqrt3_finrank.symm)
  exact sqrt3_notMem (heq ▸ IntermediateField.mem_adjoin_simple_self ℚ (Real.sqrt (3:ℝ)))

/-- `Real.sqrt 2` is integral over `ℚ⟮√3⟯`, via `X²-2`. -/
theorem sqrt2_isIntegral_over_sqrt3 :
    IsIntegral ℚ⟮Real.sqrt (3:ℝ)⟯ (Real.sqrt 2) := by
  refine ⟨X ^ 2 - C (2 : ℚ⟮Real.sqrt (3:ℝ)⟯), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  norm_num [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_ofNat,
    Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- `X² - 2` stays irreducible over `ℚ⟮√3⟯`, exactly mirroring
`X_sq_sub_three_irreducible_over_sqrt2`. -/
theorem X_sq_sub_two_irreducible_over_sqrt3 :
    Irreducible (X ^ 2 - C (2 : ℚ⟮Real.sqrt (3:ℝ)⟯)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    omega
  · intro r hr
    have hr' : r ^ 2 = 2 := by
      have h := hr
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
      exact h
    have hr'' : r * r = 2 := by rw [← sq]; exact hr'
    have hrR : (r:ℝ) * (r:ℝ) = 2 := by
      have h := congrArg (fun y : ℚ⟮Real.sqrt (3:ℝ)⟯ => (y : ℝ)) hr''
      norm_num [map_ofNat] at h
      exact h
    have h2sq' : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2); rwa [sq] at this
    have hcases : (r:ℝ) = Real.sqrt 2 ∨ (r:ℝ) = -Real.sqrt 2 :=
      mul_self_eq_mul_self_iff.mp (hrR.trans h2sq'.symm)
    apply sqrt2_notMem_sqrt3
    rcases hcases with h | h
    · rw [← h]; exact r.2
    · have : Real.sqrt 2 = -(r:ℝ) := by rw [h]; ring
      rw [this]
      exact (ℚ⟮Real.sqrt (3:ℝ)⟯ : IntermediateField ℚ ℝ).neg_mem r.2

theorem sqrt2_minpoly_over_sqrt3 :
    X ^ 2 - C (2 : ℚ⟮Real.sqrt (3:ℝ)⟯) = minpoly ℚ⟮Real.sqrt (3:ℝ)⟯ (Real.sqrt 2) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact X_sq_sub_two_irreducible_over_sqrt3
  · norm_num [map_ofNat, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  · exact monic_X_pow_sub_C _ two_ne_zero

theorem sqrt2_finrank_over_sqrt3 :
    Module.finrank ℚ⟮Real.sqrt (3:ℝ)⟯ ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank sqrt2_isIntegral_over_sqrt3,
    ← sqrt2_minpoly_over_sqrt3, natDegree_X_pow_sub_C]

theorem sqrt3_sqrt2_tower_eq :
    IntermediateField.restrictScalars ℚ
        (ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ : IntermediateField ℚ⟮Real.sqrt (3:ℝ)⟯ ℝ)
      = ℚ⟮Real.sqrt (3:ℝ), Real.sqrt (2:ℝ)⟯ :=
  adjoin_simple_adjoin_simple ℚ (Real.sqrt (3:ℝ)) (Real.sqrt (2:ℝ))

/-- `ℚ⟮√3,√2⟯ = ℚ⟮√2,√3⟯ = K`: `adjoin` only depends on the *set* of
generators, and `{√3,√2} = {√2,√3}`. -/
theorem sqrt3_sqrt2_eq_K :
    (ℚ⟮Real.sqrt (3:ℝ), Real.sqrt (2:ℝ)⟯ : IntermediateField ℚ ℝ) = K :=
  congrArg (IntermediateField.adjoin ℚ) (Set.pair_comm (Real.sqrt (3:ℝ)) (Real.sqrt (2:ℝ)))

instance : FiniteDimensional ℚ⟮Real.sqrt (3:ℝ)⟯ ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ :=
  IntermediateField.adjoin.finiteDimensional sqrt2_isIntegral_over_sqrt3

/-- σ: the automorphism of `ℚ⟮√3⟯⟮√2⟯` over base `ℚ⟮√3⟯` sending `√2 ↦ -√2`. -/
def sigma_hom : ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ →ₐ[ℚ⟮Real.sqrt (3:ℝ)⟯]
    ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ :=
  (algHomAdjoinIntegralEquiv ℚ⟮Real.sqrt (3:ℝ)⟯
    (K := ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯) sqrt2_isIntegral_over_sqrt3).symm
    ⟨-AdjoinSimple.gen ℚ⟮Real.sqrt (3:ℝ)⟯ (Real.sqrt 2), by
      rw [mem_aroots]
      refine ⟨?_, ?_⟩
      · rw [← sqrt2_minpoly_over_sqrt3]
        exact X_sq_sub_two_irreducible_over_sqrt3.ne_zero
      · rw [← sqrt2_minpoly_over_sqrt3]
        simp only [map_sub, map_pow, aeval_X, aeval_C, neg_sq]
        apply_fun (fun y : ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ => (y:ℝ))
          using Subtype.coe_injective
        push_cast [AdjoinSimple.coe_gen]
        norm_num [map_ofNat, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]⟩

def sigma_equiv_base : ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ ≃ₐ[ℚ⟮Real.sqrt (3:ℝ)⟯]
    ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯ :=
  AlgEquiv.ofBijective sigma_hom (AlgHom.bijective sigma_hom)

/-- σ, transported into an automorphism of `K` itself. -/
def sigma_K : K ≃ₐ[ℚ] K :=
  (IntermediateField.equivOfEq (sqrt3_sqrt2_tower_eq.trans sqrt3_sqrt2_eq_K)).symm.trans
    ((sigma_equiv_base.restrictScalars ℚ).trans
      (IntermediateField.equivOfEq (sqrt3_sqrt2_tower_eq.trans sqrt3_sqrt2_eq_K)))

theorem sigma_flips_sqrt2 : (sigma_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : ℝ) = -Real.sqrt (2:ℝ) := by
  simp only [sigma_K, IntermediateField.equivOfEq_symm]
  show (sigma_hom (AdjoinSimple.gen ℚ⟮Real.sqrt (3:ℝ)⟯ (Real.sqrt (2:ℝ))) : ℝ) = -Real.sqrt (2:ℝ)
  rw [sigma_hom, algHomAdjoinIntegralEquiv_symm_apply_gen]
  simp [AdjoinSimple.coe_gen]

theorem sigma_fixes_sqrt3 : (sigma_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : ℝ) = Real.sqrt (3:ℝ) := by
  simp only [sigma_K, IntermediateField.equivOfEq_symm]
  show (sigma_hom (algebraMap ℚ⟮Real.sqrt (3:ℝ)⟯ ℚ⟮Real.sqrt (3:ℝ)⟯⟮Real.sqrt (2:ℝ)⟯
      (AdjoinSimple.gen ℚ (Real.sqrt (3:ℝ)))) : ℝ) = Real.sqrt (3:ℝ)
  rw [AlgHom.commutes]
  simp [AdjoinSimple.coe_gen]

/-! ## Assembling the Klein four-group structure -/

/-- The "Phantom Middle" element: `σ` then `τ`, flipping **both** generators
simultaneously. -/
def phantom_middle : K ≃ₐ[ℚ] K := sigma_K.trans tau_K

theorem phantom_middle_sqrt2 :
    (phantom_middle ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : ℝ) = -Real.sqrt (2:ℝ) := by
  show (tau_K (sigma_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩) : ℝ) = -Real.sqrt (2:ℝ)
  have hset : sigma_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩
      = (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K) :=
    Subtype.ext sigma_flips_sqrt2
  rw [hset]
  show (tau_K ⟨-Real.sqrt (2:ℝ), _⟩ : ℝ) = -Real.sqrt (2:ℝ)
  have := tau_fixes_sqrt2
  have hneg : tau_K (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K)
      = -tau_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ := by
    have : (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K)
        = -(⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) := rfl
    rw [this, map_neg]
  rw [hneg]
  simp [tau_fixes_sqrt2]

theorem phantom_middle_sqrt3 :
    (phantom_middle ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : ℝ) = -Real.sqrt (3:ℝ) := by
  show (tau_K (sigma_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩) : ℝ) = -Real.sqrt (3:ℝ)
  have hset : sigma_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ = (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) :=
    Subtype.ext sigma_fixes_sqrt3
  rw [hset]
  exact tau_flips_sqrt3

theorem one_sqrt2 : ((1 : K ≃ₐ[ℚ] K) ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : ℝ) = Real.sqrt (2:ℝ) := rfl
theorem one_sqrt3 : ((1 : K ≃ₐ[ℚ] K) ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : ℝ) = Real.sqrt (3:ℝ) := rfl

theorem sqrt2_ne_neg : Real.sqrt (2:ℝ) ≠ -Real.sqrt (2:ℝ) := by
  have h : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro heq; rw [heq] at h; linarith

theorem sqrt3_ne_neg : Real.sqrt (3:ℝ) ≠ -Real.sqrt (3:ℝ) := by
  have h : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro heq; rw [heq] at h; linarith

theorem ne_of_sqrt2_ne {φ ψ : K ≃ₐ[ℚ] K}
    (h : (φ ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : ℝ) ≠ (ψ ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : ℝ)) :
    φ ≠ ψ := fun heq => h (by rw [heq])

theorem ne_of_sqrt3_ne {φ ψ : K ≃ₐ[ℚ] K}
    (h : (φ ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : ℝ) ≠ (ψ ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : ℝ)) :
    φ ≠ ψ := fun heq => h (by rw [heq])

theorem one_ne_sigma : (1 : K ≃ₐ[ℚ] K) ≠ sigma_K :=
  ne_of_sqrt2_ne (by rw [one_sqrt2, sigma_flips_sqrt2]; exact sqrt2_ne_neg)

theorem one_ne_tau : (1 : K ≃ₐ[ℚ] K) ≠ tau_K :=
  ne_of_sqrt3_ne (by rw [one_sqrt3, tau_flips_sqrt3]; exact sqrt3_ne_neg)

theorem one_ne_phantom : (1 : K ≃ₐ[ℚ] K) ≠ phantom_middle :=
  ne_of_sqrt2_ne (by rw [one_sqrt2, phantom_middle_sqrt2]; exact sqrt2_ne_neg)

theorem sigma_ne_tau : sigma_K ≠ tau_K :=
  ne_of_sqrt2_ne (by rw [sigma_flips_sqrt2, tau_fixes_sqrt2]; exact sqrt2_ne_neg.symm)

theorem sigma_ne_phantom : sigma_K ≠ phantom_middle :=
  ne_of_sqrt3_ne (by rw [sigma_fixes_sqrt3, phantom_middle_sqrt3]; exact sqrt3_ne_neg)

theorem tau_ne_phantom : tau_K ≠ phantom_middle :=
  ne_of_sqrt2_ne (by rw [tau_fixes_sqrt2, phantom_middle_sqrt2]; exact sqrt2_ne_neg)

/-- The four elements `{1, σ, τ, σ∘τ}` are pairwise distinct — as a `Finset`,
this has card exactly 4. -/
theorem four_elts_finset_card :
    ({1, sigma_K, tau_K, phantom_middle} : Finset (K ≃ₐ[ℚ] K)).card = 4 := by
  classical
  have h1 : (1 : K ≃ₐ[ℚ] K) ∉ ({sigma_K, tau_K, phantom_middle} : Finset (K ≃ₐ[ℚ] K)) := by
    simp [one_ne_sigma, one_ne_tau, one_ne_phantom]
  have h2 : sigma_K ∉ ({tau_K, phantom_middle} : Finset (K ≃ₐ[ℚ] K)) := by
    simp [sigma_ne_tau, sigma_ne_phantom]
  have h3 : tau_K ∉ ({phantom_middle} : Finset (K ≃ₐ[ℚ] K)) := by
    simp [tau_ne_phantom]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton]

theorem card_Gal_ge_four : 4 ≤ Fintype.card (K ≃ₐ[ℚ] K) :=
  four_elts_finset_card ▸ Finset.card_le_univ _

/-- Exactly 4 automorphisms — no more, no fewer. -/
theorem card_Gal_eq_four : Fintype.card (K ≃ₐ[ℚ] K) = 4 := by
  have hle : Fintype.card (K ≃ₐ[ℚ] K) ≤ Module.finrank ℚ K := AlgEquiv.card_le
  rw [sqrt2_sqrt3_finrank] at hle
  exact le_antisymm hle card_Gal_ge_four

theorem nat_card_Gal_eq_four : Nat.card (K ≃ₐ[ℚ] K) = 4 := by
  rw [Nat.card_eq_fintype_card, card_Gal_eq_four]

/-- **`K/ℚ` is Galois.** Not shown via constructing a splitting field, but via
the converse criterion: the automorphism count already equals the degree. -/
instance : IsGalois ℚ K :=
  IsGalois.of_card_aut_eq_finrank ℚ K
    (nat_card_Gal_eq_four.trans sqrt2_sqrt3_finrank.symm)

theorem four_elts_eq_univ :
    ({1, sigma_K, tau_K, phantom_middle} : Finset (K ≃ₐ[ℚ] K)) = Finset.univ :=
  Finset.eq_univ_of_card _ (four_elts_finset_card.trans card_Gal_eq_four.symm)

/-- Two `ℚ`-automorphisms of `K` agreeing on `√2` and `√3` are equal — `K` is
generated by exactly these two elements. -/
theorem algEquiv_ext_gens (φ ψ : K ≃ₐ[ℚ] K)
    (h2 : φ ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ = ψ ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩)
    (h3 : φ ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ = ψ ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩) :
    φ = ψ := by
  have hAlgHom : φ.toAlgHom = ψ.toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ
      (S := K) (s := ({Real.sqrt (2:ℝ), Real.sqrt (3:ℝ)} : Set ℝ)) rfl
    intro x hx
    rcases hx with h | h
    · subst h; exact h2
    · subst h; exact h3
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hAlgHom x)

/-! ## Every non-identity element has order 2 (`Monoid.exponent = 2`) -/

theorem sigma_sq : sigma_K ^ 2 = 1 := by
  apply algEquiv_ext_gens
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (sigma_K (sigma_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩) : ℝ) = Real.sqrt (2:ℝ)
    have hset : sigma_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩
        = (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K) :=
      Subtype.ext sigma_flips_sqrt2
    rw [hset]
    have hneg : (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K)
        = -(⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) := rfl
    simp [hneg, sigma_flips_sqrt2]
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (sigma_K (sigma_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩) : ℝ) = Real.sqrt (3:ℝ)
    have hset : sigma_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ = (⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) :=
      Subtype.ext sigma_fixes_sqrt3
    rw [hset, sigma_fixes_sqrt3]

theorem tau_sq : tau_K ^ 2 = 1 := by
  apply algEquiv_ext_gens
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (tau_K (tau_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩) : ℝ) = Real.sqrt (2:ℝ)
    have hset : tau_K ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ = (⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) :=
      Subtype.ext tau_fixes_sqrt2
    rw [hset, tau_fixes_sqrt2]
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (tau_K (tau_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩) : ℝ) = Real.sqrt (3:ℝ)
    have hset : tau_K ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩
        = (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K) :=
      Subtype.ext tau_flips_sqrt3
    rw [hset]
    have hneg : (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K)
        = -(⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) := rfl
    simp [hneg, tau_flips_sqrt3]

theorem phantom_sq : phantom_middle ^ 2 = 1 := by
  apply algEquiv_ext_gens
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (phantom_middle (phantom_middle ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩) : ℝ) = Real.sqrt (2:ℝ)
    have hset : phantom_middle ⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩
        = (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K) :=
      Subtype.ext phantom_middle_sqrt2
    rw [hset]
    have hneg : (⟨-Real.sqrt (2:ℝ), by simpa using neg_mem sqrt2_mem_K⟩ : K)
        = -(⟨Real.sqrt (2:ℝ), sqrt2_mem_K⟩ : K) := rfl
    simp [hneg, phantom_middle_sqrt2]
  · rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    apply Subtype.ext
    show (phantom_middle (phantom_middle ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩) : ℝ) = Real.sqrt (3:ℝ)
    have hset : phantom_middle ⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩
        = (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K) :=
      Subtype.ext phantom_middle_sqrt3
    rw [hset]
    have hneg : (⟨-Real.sqrt (3:ℝ), by simpa using neg_mem sqrt3_mem_K⟩ : K)
        = -(⟨Real.sqrt (3:ℝ), sqrt3_mem_K⟩ : K) := rfl
    simp [hneg, phantom_middle_sqrt3]

/-- Every element of `Gal(K/ℚ)` squares to `1`: the group has exactly the
four elements `{1, σ, τ, σ∘τ}` (`four_elts_eq_univ`), and each of those four
was checked individually above. -/
theorem forall_sq_eq_one : ∀ g : K ≃ₐ[ℚ] K, g ^ 2 = 1 := by
  intro g
  have hmem : g ∈ ({1, sigma_K, tau_K, phantom_middle} : Finset (K ≃ₐ[ℚ] K)) := by
    rw [four_elts_eq_univ]; exact Finset.mem_univ g
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> subst h
  · exact one_pow 2
  · exact sigma_sq
  · exact tau_sq
  · exact phantom_sq

/-- `Gal(K/ℚ)` is not trivial. -/
theorem exists_ne_one : ∃ g : K ≃ₐ[ℚ] K, g ≠ 1 := ⟨sigma_K, one_ne_sigma.symm⟩

/-- **`Monoid.exponent Gal(K/ℚ) = 2`.** Every element squares to `1`
(`forall_sq_eq_one`, so the exponent divides `2`), and the group is
non-trivial (so the exponent isn't `1`) — since `2` is prime, its only
divisors are `1` and itself, pinning the exponent down exactly. -/
theorem exponent_Gal_eq_two : Monoid.exponent (K ≃ₐ[ℚ] K) = 2 := by
  have hdvd : Monoid.exponent (K ≃ₐ[ℚ] K) ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr forall_sq_eq_one
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have hone : ∀ g : K ≃ₐ[ℚ] K, g ^ 1 = 1 := by
      have h := (Monoid.exponent_dvd_iff_forall_pow_eq_one (G := K ≃ₐ[ℚ] K) (n := 1))
      rw [h1] at h
      exact h.mp dvd_rfl
    obtain ⟨g, hg⟩ := exists_ne_one
    exact hg (by simpa using hone g)
  · exact h2

/-- **`Gal(K/ℚ)` is a Klein four-group.** -/
instance : IsKleinFour (K ≃ₐ[ℚ] K) where
  card_four := nat_card_Gal_eq_four
  exponent_two := exponent_Gal_eq_two

/-- `(1,1) ≠ 1` in `Multiplicative (ZMod 2 × ZMod 2)` — needed so the two
`setValue` adjustments below don't collide. -/
theorem ofAdd_one_one_ne_one :
    (Multiplicative.ofAdd ((1:ZMod 2), (1:ZMod 2)) : Multiplicative (ZMod 2 × ZMod 2)) ≠ 1 := by
  decide

/-- The base bijection: any cardinality-matching equivalence, with `σ∘τ`
redirected to land on `(1,1)`, then re-adjusted so `1 ↦ 1` (the two
adjustments target disjoint points, so neither disturbs the other — see
`galoisKleinFourEquiv_phantom_middle` for the case-split proving this). -/
noncomputable def galoisKleinFourBaseEquiv : (K ≃ₐ[ℚ] K) ≃ Multiplicative (ZMod 2 × ZMod 2) :=
  ((Fintype.equivOfCardEq (by
      rw [card_Gal_eq_four, Fintype.card_multiplicative, Fintype.card_prod]
      simp [ZMod.card])).setValue phantom_middle
      (Multiplicative.ofAdd (1, 1))).setValue 1 1

/-- **The explicit isomorphism to `Multiplicative (ZMod 2 × ZMod 2)`**, chosen
so the "Phantom Middle" element — the automorphism flipping *both* generators
simultaneously — lands exactly on `Multiplicative (1,1)`, per the request. -/
noncomputable def galoisKleinFourEquiv :
    (K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2 × ZMod 2) :=
  IsKleinFour.mulEquiv galoisKleinFourBaseEquiv (Equiv.setValue_eq _ 1 1)

/-- **The Phantom Middle identification, verified.** The outer `setValue 1 1`
adjustment (needed for `mulEquiv`'s identity-preserving hypothesis) does
*not* disturb `σ∘τ`'s image: `σ∘τ ≠ 1` and its image `(1,1) ≠ 1`, so the
underlying transposition swaps two points neither equal to `σ∘τ`. -/
theorem galoisKleinFourEquiv_phantom_middle :
    galoisKleinFourEquiv phantom_middle = Multiplicative.ofAdd (1, 1) := by
  set e1 : (K ≃ₐ[ℚ] K) ≃ Multiplicative (ZMod 2 × ZMod 2) :=
    (Fintype.equivOfCardEq (by
      rw [card_Gal_eq_four, Fintype.card_multiplicative, Fintype.card_prod]
      simp [ZMod.card])).setValue phantom_middle (Multiplicative.ofAdd (1, 1)) with he1
  show (e1.setValue 1 1) phantom_middle = Multiplicative.ofAdd (1, 1)
  have he1_apply : e1 phantom_middle = Multiplicative.ofAdd (1, 1) := Equiv.setValue_eq _ _ _
  have hne : phantom_middle ≠ e1.symm 1 := by
    intro h
    apply ofAdd_one_one_ne_one
    have := congrArg e1 h
    rwa [Equiv.apply_symm_apply, he1_apply] at this
  show ((Equiv.swap 1 (e1.symm 1)).trans e1) phantom_middle = Multiplicative.ofAdd (1, 1)
  rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm one_ne_phantom) hne, he1_apply]

end
