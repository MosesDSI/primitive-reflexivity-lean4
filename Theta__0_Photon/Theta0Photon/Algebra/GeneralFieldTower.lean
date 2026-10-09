import Theta0Photon.Algebra.FieldTower

/-!
# General Field Tower: `[ℚ(√d₁, √d₂) : ℚ] = 4` for any independent non-square pair

`FieldTower.lean` closes the degree-4 tower `[ℚ(√2,√3):ℚ] = 4` for the fixed
pair `(2,3)`. This file reruns that same argument — unchanged in shape — for
an arbitrary pair `d₁ d₂ : ℕ` satisfying the independence condition from the
`Instructure` companion definition:

* `¬ IsSquare d₁`
* `¬ IsSquare d₂`
* `¬ IsSquare (d₁ * d₂)`

Everything in `FieldTower.lean`'s §1 (`sqrt_isIntegral`, `sqrt_minpoly`,
`sqrt_finrank`, `sqrt_ne_ratCast`) is already stated for an arbitrary
non-square `d`, so it is reused here directly, unchanged. What's new is
reproving §2 (the independence fact `√d₂ ∉ ℚ⟮√d₁⟯`) and §3 (closing the
tower via the tower law) with `d₁, d₂` as free variables instead of the
literals `2, 3`.

No new mathematical content: every step below is the same case split and the
same tower-law computation as the `(2,3)` instance, with `2 ↦ d₁`, `3 ↦ d₂`,
`6 ↦ d₁·d₂` throughout. The only genuinely new move is in the `a = 0` case of
the independence proof, where the concrete `(2c)² = 6` step is replaced by
its general form `(c·d₁)² = d₁·d₂`, derived the same way.
-/

open Polynomial IntermediateField

noncomputable section

namespace Theta0Photon.GeneralFieldTower

/-- Bridge from Mathlib's `IsSquare` (`∃ r, d = r * r`) to the
`∃ k, k * k = d` form `FieldTower.lean`'s lemmas are stated against. -/
theorem not_exists_sq_of_not_isSquare {d : ℕ} (hd : ¬ IsSquare d) :
    ¬ ∃ k : ℕ, k * k = d :=
  fun ⟨k, hk⟩ => hd ⟨k, hk.symm⟩

/-- The converse bridge, used to recover `¬ IsSquare` for the concrete
`(2,3)` sanity check from `FieldTower.lean`'s `two_not_square` /
`three_not_square` / `six_not_square` (stated in the `∃k,k*k=d` form, since
`decide` doesn't reduce `Nat.sqrt`'s well-founded recursion in the kernel). -/
theorem not_isSquare_of_not_exists_sq {d : ℕ} (hd : ¬ ∃ k : ℕ, k * k = d) :
    ¬ IsSquare d :=
  fun ⟨r, hr⟩ => hd ⟨r, hr.symm⟩

/-- No rational number squares to a non-square natural `d` — the same fact
`sqrt_ne_ratCast` restates for `Real.sqrt`, used here directly on rationals
(no square root needed) for the `a = 0` case below. -/
theorem no_rat_sq {d : ℕ} (hd : ¬ IsSquare d) (r : ℚ) : r * r ≠ (d : ℚ) := by
  intro h
  exact triadic_no_rational_root d (not_exists_sq_of_not_isSquare hd) r
    (by simp [eval_sub, eval_X, sq, h])

/-!
## §1′ — The quadratic layer, instantiated via `IsSquare`

Thin wrappers around `FieldTower.lean`'s already-general `sqrt_finrank`, so
the rest of this file can be stated uniformly against `¬ IsSquare`.
-/

theorem sqrt_finrank' {d : ℕ} (hd : ¬ IsSquare d) :
    Module.finrank ℚ ℚ⟮Real.sqrt (d : ℝ)⟯ = 2 :=
  sqrt_finrank d (not_exists_sq_of_not_isSquare hd)

/-!
## §2′ — The independence fact, for general `(d₁, d₂)`: `√d₂ ∉ ℚ⟮√d₁⟯`

Exactly `FieldTower.lean`'s §2 argument: build the explicit basis `{1, √d₁}`
of `ℚ⟮√d₁⟯`, then case-split an assumed `√d₂ = a + c√d₁` on whether `a` or `c`
vanishes, each case forcing a rational square root of `d₁`, `d₂`, or
`d₁·d₂` — ruled out by the three hypotheses.
-/

/-- `{1, √d₁}` is `ℚ`-linearly independent in `ℚ⟮√d₁⟯`. -/
theorem sqrt_basis_indep {d₁ : ℕ} (hd1 : ¬ IsSquare d₁) :
    LinearIndependent ℚ
      (![1, AdjoinSimple.gen ℚ (Real.sqrt (d₁ : ℝ))] : Fin 2 → ℚ⟮Real.sqrt (d₁ : ℝ)⟯) := by
  rw [LinearIndependent.pair_iff' one_ne_zero]
  intro a ha
  apply sqrt_ne_ratCast d₁ (not_exists_sq_of_not_isSquare hd1) a
  have h := congrArg (fun y : ℚ⟮Real.sqrt (d₁ : ℝ)⟯ => (y : ℝ)) ha
  simpa [Algebra.smul_def, AdjoinSimple.coe_gen] using h

/-- The resulting basis `{1, √d₁}` of `ℚ⟮√d₁⟯` over `ℚ`. -/
def sqrt_basis {d₁ : ℕ} (hd1 : ¬ IsSquare d₁) :
    Module.Basis (Fin 2) ℚ ℚ⟮Real.sqrt (d₁ : ℝ)⟯ :=
  basisOfLinearIndependentOfCardEqFinrank (sqrt_basis_indep hd1) (by simp [sqrt_finrank' hd1])

/-- Every element of `ℚ⟮√d₁⟯` has the form `a + c√d₁` for rationals `a, c`. -/
theorem sqrt_field_eq {d₁ : ℕ} (hd1 : ¬ IsSquare d₁) (x : ℚ⟮Real.sqrt (d₁ : ℝ)⟯) :
    ∃ a c : ℚ, (x : ℝ) = (a : ℝ) + (c : ℝ) * Real.sqrt d₁ := by
  refine ⟨(sqrt_basis hd1).repr x 0, (sqrt_basis hd1).repr x 1, ?_⟩
  have h := (sqrt_basis hd1).sum_repr x
  rw [Fin.sum_univ_two] at h
  have hc := congrArg (fun y : ℚ⟮Real.sqrt (d₁ : ℝ)⟯ => (y : ℝ)) h.symm
  simpa [sqrt_basis, coe_basisOfLinearIndependentOfCardEqFinrank,
    AdjoinSimple.coe_gen, Algebra.smul_def] using hc

/-- **The general independence fact.** For `d₁, d₂` with `d₁`, `d₂`, and
`d₁·d₂` all non-square, `√d₂` cannot already be an element of `ℚ⟮√d₁⟯`. -/
theorem sqrt_notMem {d₁ d₂ : ℕ} (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Real.sqrt d₂ ∉ (ℚ⟮Real.sqrt (d₁ : ℝ)⟯ : IntermediateField ℚ ℝ) := by
  intro hmem
  obtain ⟨a, c, hac⟩ := sqrt_field_eq hd1 (⟨Real.sqrt d₂, hmem⟩ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯)
  have hac' : Real.sqrt d₂ = (a : ℝ) + (c : ℝ) * Real.sqrt d₁ := hac
  have hd2sq : Real.sqrt (d₂ : ℝ) ^ 2 = (d₂ : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d₂)
  have hd1sq : Real.sqrt (d₁ : ℝ) ^ 2 = (d₁ : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d₁)
  have hsq : (d₂ : ℝ) = (a : ℝ) ^ 2 + 2 * (a : ℝ) * (c : ℝ) * Real.sqrt d₁
      + (c : ℝ) ^ 2 * (d₁ : ℝ) := by
    have e1 : ((a : ℝ) + (c : ℝ) * Real.sqrt d₁) ^ 2
        = (a : ℝ) ^ 2 + 2 * (a : ℝ) * (c : ℝ) * Real.sqrt d₁
          + (c : ℝ) ^ 2 * Real.sqrt (d₁ : ℝ) ^ 2 := by ring
    rw [hd1sq, ← hac', hd2sq] at e1
    linarith [e1]
  by_cases hc0 : c = 0
  · -- c = 0: √d₂ = a, a rational — contradicts irrationality of √d₂ directly.
    rw [hc0] at hac'
    simp at hac'
    exact sqrt_ne_ratCast d₂ (not_exists_sq_of_not_isSquare hd2) a hac'.symm
  · by_cases ha0 : a = 0
    · -- a = 0: √d₂ = c√d₁. Derive a rational square root of d₁·d₂.
      rw [ha0] at hac'
      simp at hac'
      have hc2 : (c : ℝ) ^ 2 * (d₁ : ℝ) = (d₂ : ℝ) := by
        have e2 : Real.sqrt (d₂ : ℝ) ^ 2 = ((c : ℝ) * Real.sqrt d₁) ^ 2 := by rw [hac']
        rw [hd2sq, mul_pow, hd1sq] at e2
        linarith [e2]
      have hprod : ((c : ℝ) * (d₁ : ℝ)) ^ 2 = (d₁ : ℝ) * (d₂ : ℝ) := by
        have e3 : ((c : ℝ) * (d₁ : ℝ)) ^ 2 = (c : ℝ) ^ 2 * (d₁ : ℝ) * (d₁ : ℝ) := by ring
        rw [e3, hc2]; ring
      apply no_rat_sq hd12 (c * d₁)
      have hcast : ((c * (d₁ : ℚ)) * (c * (d₁ : ℚ)) : ℝ) = ((d₁ * d₂ : ℚ) : ℝ) := by
        push_cast
        rw [← sq]
        linarith [hprod]
      exact_mod_cast hcast
    · -- a ≠ 0, c ≠ 0: isolate √d₁ as an explicit rational number.
      have ha0' : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
      have hc0' : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
      have hac2_ne : (2 : ℝ) * (a : ℝ) * (c : ℝ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero ha0') hc0'
      apply sqrt_ne_ratCast d₁ (not_exists_sq_of_not_isSquare hd1)
        ((d₂ - a ^ 2 - c ^ 2 * d₁) / (2 * a * c))
      push_cast
      rw [div_eq_iff hac2_ne]
      nlinarith [hsq]

/-!
## §3′ — Closing the general degree-4 tower

Exactly `FieldTower.lean`'s §3: `X² - d₂` stays irreducible over the bigger
base field `ℚ⟮√d₁⟯`, because a root there would put `√d₂ ∈ ℚ⟮√d₁⟯`,
contradicting `sqrt_notMem`. This gives `minpoly ℚ⟮√d₁⟯ (√d₂) = X²-d₂`, hence
`[ℚ⟮√d₁⟯⟮√d₂⟯:ℚ⟮√d₁⟯] = 2`, and the tower law finishes
`[ℚ(√d₁,√d₂):ℚ] = 2·2 = 4`.
-/

theorem sqrt_isIntegral_over {d₁ d₂ : ℕ} :
    IsIntegral ℚ⟮Real.sqrt (d₁ : ℝ)⟯ (Real.sqrt d₂) := by
  refine ⟨X ^ 2 - C (d₂ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  norm_num [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_natCast,
    Real.sq_sqrt (Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂)]

theorem X_sq_sub_irreducible_over {d₁ d₂ : ℕ} (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Irreducible (X ^ 2 - C (d₂ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    omega
  · intro r hr
    have hr' : r ^ 2 = (d₂ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯) := by
      have h := hr
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
      exact h
    have hr'' : r * r = (d₂ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯) := by rw [← sq]; exact hr'
    have hrR : (r : ℝ) * (r : ℝ) = (d₂ : ℝ) := by
      have h := congrArg (fun y : ℚ⟮Real.sqrt (d₁ : ℝ)⟯ => (y : ℝ)) hr''
      norm_num [map_natCast] at h
      exact h
    have hd2sq' : Real.sqrt (d₂ : ℝ) * Real.sqrt (d₂ : ℝ) = (d₂ : ℝ) := by
      have := Real.sq_sqrt (Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂); rwa [sq] at this
    have hcases : (r : ℝ) = Real.sqrt d₂ ∨ (r : ℝ) = -Real.sqrt d₂ :=
      mul_self_eq_mul_self_iff.mp (hrR.trans hd2sq'.symm)
    apply sqrt_notMem hd1 hd2 hd12
    rcases hcases with h | h
    · rw [← h]; exact r.2
    · have : Real.sqrt (d₂ : ℝ) = -(r : ℝ) := by rw [h]; ring
      rw [this]
      exact (ℚ⟮Real.sqrt (d₁ : ℝ)⟯ : IntermediateField ℚ ℝ).neg_mem r.2

theorem sqrt_minpoly_over {d₁ d₂ : ℕ} (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    X ^ 2 - C (d₂ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯) = minpoly ℚ⟮Real.sqrt (d₁ : ℝ)⟯ (Real.sqrt d₂) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact X_sq_sub_irreducible_over hd1 hd2 hd12
  · norm_num [map_natCast, Real.sq_sqrt (Nat.cast_nonneg d₂ : (0:ℝ) ≤ d₂)]
  · exact monic_X_pow_sub_C _ two_ne_zero

theorem sqrt_finrank_over {d₁ d₂ : ℕ} (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Module.finrank ℚ⟮Real.sqrt (d₁ : ℝ)⟯ ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank sqrt_isIntegral_over,
    ← sqrt_minpoly_over hd1 hd2 hd12, natDegree_X_pow_sub_C]

theorem sqrt_sqrt_tower_eq {d₁ d₂ : ℕ} :
    IntermediateField.restrictScalars ℚ
        (ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ :
          IntermediateField ℚ⟮Real.sqrt (d₁ : ℝ)⟯ ℝ)
      = ℚ⟮Real.sqrt (d₁ : ℝ), Real.sqrt (d₂ : ℝ)⟯ :=
  adjoin_simple_adjoin_simple ℚ (Real.sqrt (d₁ : ℝ)) (Real.sqrt (d₂ : ℝ))

/-- **The general degree-4 tower.** For any `d₁, d₂ : ℕ` with `d₁`, `d₂`, and
`d₁·d₂` all non-square, `[ℚ(√d₁,√d₂):ℚ] = 4`, computed exactly via the tower
law. This is the `(2,3)`-instance `sqrt2_sqrt3_finrank` with the pair made a
free variable — same proof, same mechanism. -/
theorem sqrt_sqrt_finrank {d₁ d₂ : ℕ} (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Module.finrank ℚ ℚ⟮Real.sqrt (d₁ : ℝ), Real.sqrt (d₂ : ℝ)⟯ = 4 := by
  rw [← sqrt_sqrt_tower_eq]
  show Module.finrank ℚ ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯ = 4
  rw [← Module.finrank_mul_finrank ℚ ℚ⟮Real.sqrt (d₁ : ℝ)⟯
      ℚ⟮Real.sqrt (d₁ : ℝ)⟯⟮Real.sqrt (d₂ : ℝ)⟯,
    sqrt_finrank_over hd1 hd2 hd12, sqrt_finrank' hd1]

/-- **Sanity check: specializes to the `(2,3)` instance.** Reruns
`FieldTower.lean`'s concrete `sqrt2_sqrt3_finrank` result through this file's
general theorem, confirming the generalization doesn't silently diverge from
the instance it generalizes. -/
theorem sqrt2_sqrt3_finrank_via_general :
    Module.finrank ℚ ℚ⟮Real.sqrt (2 : ℝ), Real.sqrt (3 : ℝ)⟯ = 4 :=
  sqrt_sqrt_finrank (d₁ := 2) (d₂ := 3)
    (not_isSquare_of_not_exists_sq two_not_square)
    (not_isSquare_of_not_exists_sq three_not_square)
    (not_isSquare_of_not_exists_sq six_not_square)

end Theta0Photon.GeneralFieldTower

end

#print axioms Theta0Photon.GeneralFieldTower.sqrt_finrank'
#print axioms Theta0Photon.GeneralFieldTower.sqrt_notMem
#print axioms Theta0Photon.GeneralFieldTower.sqrt_sqrt_finrank
#print axioms Theta0Photon.GeneralFieldTower.sqrt2_sqrt3_finrank_via_general
