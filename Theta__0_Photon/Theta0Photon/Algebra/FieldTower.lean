import Theta0Photon.Algebra.GroundAxiom
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Field Tower: the Degree-4 Biquadratic Tower from the Ground Axiom

**Status: the degree-4 tower is closed; the Galois-group/Klein-four/"Phantom
Middle" layer is not yet built on top of it.** This file rigorously builds,
for the concrete pair `d₁ = 2, d₂ = 3` (squarefree, distinct, and
multiplicatively independent — `2·3 = 6` is checked non-square too, which is
exactly the condition the independence step below needs):

* the quadratic layer `ℚ⟮√d⟯/ℚ` for any squarefree `d`, using
  `triadic_ground_irreducible` from `GroundAxiom.lean` as the actual mechanism
  that computes its degree (§1);
* the genuine independence fact `√3 ∉ ℚ⟮√2⟯` (§2), proved via an explicit
  `{1,√2}` basis of `ℚ⟮√2⟯` and a classical case split — not assumed;
* the resulting degree-4 tower `[ℚ(√2,√3):ℚ] = 4`, computed exactly via the
  tower law (§3).

No theorem beyond this is stated. The automorphism/Galois-group/Klein-four
layer is its own separate, substantial stage — see the closing module doc for
exactly what it needs and what Mathlib machinery for it was already located
this session.

## §1 — The quadratic layer, for any squarefree `d`

* `sqrt_isIntegral d` — `Real.sqrt d` is integral over `ℚ`, witnessed by the
  monic polynomial `X² - d`.
* `sqrt_minpoly d hd` — `X² - C d` **is** `minpoly ℚ (Real.sqrt d)`. The
  genuine, non-decorative use of the ground axiom: identifying a minimal
  polynomial requires irreducibility, and `triadic_ground_irreducible` is
  exactly the fact that supplies it.
* `sqrt_finrank d hd` — hence `[ℚ⟮√d⟯ : ℚ] = 2` exactly.
-/

open Polynomial IntermediateField

noncomputable section

/-- `Real.sqrt d` is a root of the monic polynomial `X² - d`, hence integral
over `ℚ`, for any natural `d`. (No squarefreeness needed for integrality
itself — only for identifying the *minimal* polynomial next.) -/
theorem sqrt_isIntegral (d : ℕ) : IsIntegral ℚ (Real.sqrt d) := by
  refine ⟨X ^ 2 - C (d : ℚ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  simp [Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)]

/-- The genuine use of the ground axiom: `X² - C d` is not merely *a* monic
polynomial with `√d` as a root, it is *the* minimal polynomial — because
`triadic_ground_irreducible` supplies the irreducibility that
`minpoly.eq_of_irreducible_of_monic` requires. -/
theorem sqrt_minpoly (d : ℕ) (hd : ¬ ∃ k : ℕ, k * k = d) :
    X ^ 2 - C (d : ℚ) = minpoly ℚ (Real.sqrt d) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact triadic_ground_irreducible d hd
  · simp [Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  · exact monic_X_pow_sub_C _ two_ne_zero

/-- `[ℚ⟮√d⟯ : ℚ] = 2` for any non-square natural `d`, computed exactly from
the ground axiom via the minimal-polynomial identification above. -/
theorem sqrt_finrank (d : ℕ) (hd : ¬ ∃ k : ℕ, k * k = d) :
    Module.finrank ℚ ℚ⟮Real.sqrt (d:ℝ)⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank (sqrt_isIntegral d), ← sqrt_minpoly d hd,
    natDegree_X_pow_sub_C]

/-! ## Instantiated at the concrete pair from the request: `d₁ = 2`, `d₂ = 3` -/

/-- `d₁ = 2` is squarefree (non-square): witnessed by exhaustive decision, not
assumed. -/
theorem two_not_square : ¬ ∃ k : ℕ, k * k = 2 := by
  rintro ⟨k, hk⟩
  have : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

/-- `d₂ = 3` is squarefree (non-square). -/
theorem three_not_square : ¬ ∃ k : ℕ, k * k = 3 := by
  rintro ⟨k, hk⟩
  have : k ≤ 3 := by nlinarith
  interval_cases k <;> omega

/-- `d₁ · d₂ = 6` is also non-square — this is exactly the "multiplicatively
independent" condition from the request, restated computationally: `√6` is
irrational too, which is exactly what §2's independence proof needs. -/
theorem six_not_square : ¬ ∃ k : ℕ, k * k = 6 := by
  rintro ⟨k, hk⟩
  have : k ≤ 6 := by nlinarith
  interval_cases k <;> omega

theorem sqrt2_finrank : Module.finrank ℚ ℚ⟮Real.sqrt (2:ℝ)⟯ = 2 :=
  sqrt_finrank 2 two_not_square

theorem sqrt3_finrank : Module.finrank ℚ ℚ⟮Real.sqrt (3:ℝ)⟯ = 2 :=
  sqrt_finrank 3 three_not_square

/-!
## §2 — The independence fact: `√3 ∉ ℚ⟮√2⟯`

This is the actual content of "multiplicative independence," proved rather
than assumed: an explicit `ℚ`-basis `{1, √2}` of `ℚ⟮√2⟯` is built (via
`LinearIndependent.pair_iff'` + `basisOfLinearIndependentOfCardEqFinrank`),
giving every element of `ℚ⟮√2⟯` the form `a + c√2`. A classical case split on
`a + c√2 = √3` — clearing `√2` when `a·c ≠ 0`, otherwise splitting `a = 0` vs
`c = 0` — forces a rational square root of 2, 3, or 6, each ruled out by
`sqrt_ne_ratCast` (built directly on `triadic_no_rational_root`, the same
ground-axiom lemma underlying §1).
-/

/-- No rational number equals `Real.sqrt d`, for non-square `d`. The direct
real-number-level restatement of `triadic_no_rational_root`. -/
theorem sqrt_ne_ratCast (d : ℕ) (hd : ¬ ∃ k : ℕ, k * k = d) (a : ℚ) :
    (a : ℝ) ≠ Real.sqrt d := by
  intro h
  apply triadic_no_rational_root d hd a
  have h1 : (a : ℝ) ^ 2 = (d : ℝ) := by rw [h]; exact Real.sq_sqrt (Nat.cast_nonneg d)
  have h2 : (a ^ 2 : ℚ) = (d : ℚ) := by exact_mod_cast h1
  simp [eval_sub, eval_pow, eval_X, h2]

/-- `{1, gen}` is `ℚ`-linearly independent in `ℚ⟮√2⟯`. -/
theorem sqrt2_basis_indep :
    LinearIndependent ℚ
      (![1, AdjoinSimple.gen ℚ (Real.sqrt (2:ℝ))] : Fin 2 → ℚ⟮Real.sqrt (2:ℝ)⟯) := by
  rw [LinearIndependent.pair_iff' one_ne_zero]
  intro a ha
  apply sqrt_ne_ratCast 2 two_not_square a
  have h := congrArg (fun y : ℚ⟮Real.sqrt (2:ℝ)⟯ => (y : ℝ)) ha
  simp only [Algebra.smul_def, mul_one, AdjoinSimple.coe_gen] at h
  have h2 : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
  rw [h2, ← h]
  norm_cast

/-- The resulting basis `{1, √2}` of `ℚ⟮√2⟯` over `ℚ`. -/
def sqrt2_basis : Module.Basis (Fin 2) ℚ ℚ⟮Real.sqrt (2:ℝ)⟯ :=
  basisOfLinearIndependentOfCardEqFinrank sqrt2_basis_indep (by simp [sqrt2_finrank])

/-- Every element of `ℚ⟮√2⟯` has the form `a + c√2` for rationals `a, c`. -/
theorem sqrt2_field_eq (x : ℚ⟮Real.sqrt (2:ℝ)⟯) :
    ∃ a c : ℚ, (x : ℝ) = (a : ℝ) + (c : ℝ) * Real.sqrt 2 := by
  refine ⟨sqrt2_basis.repr x 0, sqrt2_basis.repr x 1, ?_⟩
  have h := sqrt2_basis.sum_repr x
  rw [Fin.sum_univ_two] at h
  have hc := congrArg (fun y : ℚ⟮Real.sqrt (2:ℝ)⟯ => (y : ℝ)) h.symm
  simpa [sqrt2_basis, coe_basisOfLinearIndependentOfCardEqFinrank,
    AdjoinSimple.coe_gen, Algebra.smul_def] using hc

/-- **The independence fact.** `√3` cannot already be an element of `ℚ⟮√2⟯`. -/
theorem sqrt3_notMem : Real.sqrt 3 ∉ (ℚ⟮Real.sqrt (2:ℝ)⟯ : IntermediateField ℚ ℝ) := by
  intro hmem
  obtain ⟨a, c, hac⟩ := sqrt2_field_eq (⟨Real.sqrt 3, hmem⟩ : ℚ⟮Real.sqrt (2:ℝ)⟯)
  have hac' : Real.sqrt 3 = (a:ℝ) + (c:ℝ) * Real.sqrt 2 := hac
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (3:ℝ) = (a:ℝ) ^ 2 + 2 * (a:ℝ) * (c:ℝ) * Real.sqrt 2 + 2 * (c:ℝ) ^ 2 := by
    have e1 : ((a:ℝ) + (c:ℝ) * Real.sqrt 2) ^ 2
        = (a:ℝ) ^ 2 + 2 * (a:ℝ) * (c:ℝ) * Real.sqrt 2 + (c:ℝ) ^ 2 * Real.sqrt 2 ^ 2 := by
      ring
    rw [h2sq, ← hac', h3sq] at e1
    linarith [e1]
  by_cases hc0 : c = 0
  · -- c = 0: √3 = a, a rational — contradicts irrationality of √3 directly.
    rw [hc0] at hac'
    simp at hac'
    have h3cast : ((3:ℕ):ℝ) = (3:ℝ) := by norm_num
    exact sqrt_ne_ratCast 3 three_not_square a (by rw [h3cast]; exact hac'.symm)
  · by_cases ha0 : a = 0
    · -- a = 0: √3 = c√2. Derive a rational square root of 6.
      rw [ha0] at hac'
      simp at hac'
      have hc_nonneg : (0:ℝ) ≤ (c:ℝ) := by
        by_contra hneg
        push Not at hneg
        have hneg' : (c:ℝ) * Real.sqrt 2 < 0 :=
          mul_neg_of_neg_of_pos hneg (Real.sqrt_pos.mpr (by norm_num))
        rw [← hac'] at hneg'
        exact absurd hneg' (not_lt.mpr (Real.sqrt_nonneg 3))
      have hc2 : (c:ℝ) ^ 2 * 2 = 3 := by
        have e2 : Real.sqrt 3 ^ 2 = ((c:ℝ) * Real.sqrt 2) ^ 2 := by rw [hac']
        rw [h3sq, mul_pow, h2sq] at e2
        linarith [e2]
      have hsix : (2 * (c:ℝ)) ^ 2 = 6 := by
        have e3 : (2 * (c:ℝ)) ^ 2 = (c:ℝ) ^ 2 * 2 * 2 := by ring
        rw [e3, hc2]
        norm_num
      have heq6 : (2 * (c:ℝ)) = Real.sqrt 6 := by
        rw [← hsix]; exact (Real.sqrt_sq (by linarith)).symm
      apply sqrt_ne_ratCast 6 six_not_square (2 * c)
      push_cast
      linarith [heq6]
    · -- a ≠ 0, c ≠ 0: isolate √2 as an explicit rational number.
      have ha0' : (a:ℝ) ≠ 0 := by exact_mod_cast ha0
      have hc0' : (c:ℝ) ≠ 0 := by exact_mod_cast hc0
      have hac2_ne : (2:ℝ) * (a:ℝ) * (c:ℝ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero ha0') hc0'
      apply sqrt_ne_ratCast 2 two_not_square ((3 - a ^ 2 - 2 * c ^ 2) / (2 * a * c))
      push_cast
      rw [div_eq_iff hac2_ne]
      nlinarith [hsq]

/-!
## §3 — Closing the degree-4 tower

The independence fact re-runs exactly the §1 pattern one level up: `X²-3`
stays irreducible over the bigger base field `ℚ⟮√2⟯` (not just over `ℚ`)
because a root there would put `√3 ∈ ℚ⟮√2⟯`, contradicting §2. This gives
`minpoly ℚ⟮√2⟯ (√3) = X²-3` exactly as in §1, hence `[ℚ⟮√2⟯⟮√3⟯:ℚ⟮√2⟯] = 2`,
and the tower law finishes `[ℚ(√2,√3):ℚ] = 2·2 = 4`.
-/

/-- `Real.sqrt 3` is integral over `ℚ⟮√2⟯`, via the same monic witness `X²-3`,
now viewed as a polynomial over the bigger base field. -/
theorem sqrt3_isIntegral_over_sqrt2 :
    IsIntegral ℚ⟮Real.sqrt (2:ℝ)⟯ (Real.sqrt 3) := by
  refine ⟨X ^ 2 - C (3 : ℚ⟮Real.sqrt (2:ℝ)⟯), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  norm_num [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_ofNat,
    Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- `X² - 3` stays irreducible over `ℚ⟮√2⟯` — the genuine content of
"multiplicative independence," now proved rather than assumed. Any root
`r : ℚ⟮√2⟯` would coerce to a real number with `r² = 3`, forcing
`r = ±√3` as reals, and either sign puts `√3 ∈ ℚ⟮√2⟯` (the field is closed
under negation) — contradicting `sqrt3_notMem`. -/
theorem X_sq_sub_three_irreducible_over_sqrt2 :
    Irreducible (X ^ 2 - C (3 : ℚ⟮Real.sqrt (2:ℝ)⟯)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    omega
  · intro r hr
    have hr' : r ^ 2 = 3 := by
      have h := hr
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
      exact h
    have hr'' : r * r = 3 := by rw [← sq]; exact hr'
    have hrR : (r:ℝ) * (r:ℝ) = 3 := by
      have h := congrArg (fun y : ℚ⟮Real.sqrt (2:ℝ)⟯ => (y : ℝ)) hr''
      norm_num [map_ofNat] at h
      exact h
    have h3sq' : Real.sqrt 3 * Real.sqrt 3 = 3 := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3); rwa [sq] at this
    have hcases : (r:ℝ) = Real.sqrt 3 ∨ (r:ℝ) = -Real.sqrt 3 :=
      mul_self_eq_mul_self_iff.mp (hrR.trans h3sq'.symm)
    apply sqrt3_notMem
    rcases hcases with h | h
    · rw [← h]; exact r.2
    · have : Real.sqrt 3 = -(r:ℝ) := by rw [h]; ring
      rw [this]
      exact (ℚ⟮Real.sqrt (2:ℝ)⟯ : IntermediateField ℚ ℝ).neg_mem r.2

/-- `X² - 3` **is** `minpoly ℚ⟮√2⟯ (√3)` — the genuine use of the
independence fact, exactly mirroring how the ground axiom identifies
`minpoly ℚ (√d)` in §1. -/
theorem sqrt3_minpoly_over_sqrt2 :
    X ^ 2 - C (3 : ℚ⟮Real.sqrt (2:ℝ)⟯) = minpoly ℚ⟮Real.sqrt (2:ℝ)⟯ (Real.sqrt 3) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact X_sq_sub_three_irreducible_over_sqrt2
  · norm_num [map_ofNat, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  · exact monic_X_pow_sub_C _ two_ne_zero

/-- `[ℚ⟮√2⟯⟮√3⟯ : ℚ⟮√2⟯] = 2`. -/
theorem sqrt3_finrank_over_sqrt2 :
    Module.finrank ℚ⟮Real.sqrt (2:ℝ)⟯ ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank sqrt3_isIntegral_over_sqrt2,
    ← sqrt3_minpoly_over_sqrt2, natDegree_X_pow_sub_C]

/-- `ℚ⟮√2⟯⟮√3⟯` (as a `ℚ`-intermediate field of `ℝ`, via `restrictScalars`)
is exactly `ℚ⟮√2,√3⟯`. -/
theorem sqrt2_sqrt3_tower_eq :
    IntermediateField.restrictScalars ℚ
        (ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ : IntermediateField ℚ⟮Real.sqrt (2:ℝ)⟯ ℝ)
      = ℚ⟮Real.sqrt (2:ℝ), Real.sqrt (3:ℝ)⟯ :=
  adjoin_simple_adjoin_simple ℚ (Real.sqrt (2:ℝ)) (Real.sqrt (3:ℝ))

/-- **The degree-4 tower, closed.** `[ℚ(√2,√3) : ℚ] = 4`, computed exactly
via the tower law: `[ℚ⟮√2,√3⟯:ℚ] = [ℚ⟮√2⟯⟮√3⟯:ℚ⟮√2⟯] · [ℚ⟮√2⟯:ℚ] = 2 · 2`. -/
theorem sqrt2_sqrt3_finrank :
    Module.finrank ℚ ℚ⟮Real.sqrt (2:ℝ), Real.sqrt (3:ℝ)⟯ = 4 := by
  rw [← sqrt2_sqrt3_tower_eq]
  show Module.finrank ℚ ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯ = 4
  rw [← Module.finrank_mul_finrank ℚ ℚ⟮Real.sqrt (2:ℝ)⟯
      ℚ⟮Real.sqrt (2:ℝ)⟯⟮Real.sqrt (3:ℝ)⟯,
    sqrt3_finrank_over_sqrt2, sqrt2_finrank]

end

/-!
## What's still needed for `Gal(ℚ(√2,√3)/ℚ) ≅ V₄` and the Phantom Middle element

Not stated as a theorem anywhere in this file — this is the honest remainder,
not a claim. With `sqrt2_sqrt3_finrank` in hand, the path is:

1. Show `IsGalois ℚ ℚ⟮√2,√3⟯` (normal + separable — separable is automatic in
   characteristic 0; normal follows from `ℚ⟮√2,√3⟯` being the splitting field
   of `(X²-2)(X²-3)`, which needs the four roots `±√2,±√3` all lying in the
   field, immediate from closure under negation).
2. `IsGalois.card_aut_eq_finrank` then gives `Nat.card Gal(ℚ⟮√2,√3⟯/ℚ) = 4`.
3. Construct the two sign-flip `AlgEquiv`s explicitly (fixing `ℚ`, sending
   `√2 ↦ -√2` and/or `√3 ↦ -√3`) and show every non-identity element has
   order 2, giving `Monoid.exponent = 2`.
4. `IsKleinFour` (`Mathlib.GroupTheory.SpecificGroups.KleinFour`) then applies:
   `Nat.card = 4 ∧ exponent = 2` is exactly its definition, and
   `IsKleinFour.mulEquiv'` builds an explicit isomorphism to
   `Multiplicative (ZMod 2 × ZMod 2)` from any identity-preserving bijection —
   the natural choice sends the automorphism flipping *both* generators
   (`√2↦-√2, √3↦-√3` simultaneously) to `Multiplicative (1,1)`, which is the
   requested "Phantom Middle" element.

All four Mathlib pieces named above were located and confirmed present in
this Mathlib revision during this session's research; none of them has yet
been applied to an actual proof term in this file.
-/
