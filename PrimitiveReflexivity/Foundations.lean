import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Circle

set_option linter.style.header false
set_option linter.unusedVariables false

namespace PrimitiveReflexivity

/- =====================================================================
   SECTION I & II: The Primordial Node Field and Axioms of Reflexivity
   ===================================================================== -/

variable {N : Type}
variable (R : N → N → Prop)

class LocalizedReflexive (R : N → N → Prop) : Prop where
  refl (x : N) : R x x

theorem reflexive_minimality
    (R S : N → N → Prop)
    [instR : LocalizedReflexive R]
    (hS : ∀ x : N, S x x) :
    ∀ x : N, R x x → S x x := by
  intro x _
  exact hS x

theorem reflexive_isomorphism
    {N1 N2 : Type}
    (R1 : N1 → N1 → Prop)
    (R2 : N2 → N2 → Prop)
    [LocalizedReflexive R1]
    [LocalizedReflexive R2]
    (f : N1 ≃ N2) :
    ∀ x : N1, R1 x x ↔ R2 (f x) (f x) := by
  intro x
  constructor
  · intro _
    exact LocalizedReflexive.refl (f x)
  · intro _
    exact LocalizedReflexive.refl x

/- =====================================================================
   SECTION IV & V: Arithmetic Descent and Prime Per Se Identity
   ===================================================================== -/

def DivSet (p : ℕ) : Set ℕ := { d : ℕ | d ∣ p }

def ArithmeticPerSeIdentity (p : ℕ) : Prop :=
  p > 1 ∧ DivSet p = {1, p}

theorem prime_incompressibility (p : ℕ) :
    Nat.Prime p ↔ ArithmeticPerSeIdentity p := by
  constructor
  · intro hprime
    have hp_gt1 : p > 1 := Nat.Prime.one_lt hprime
    constructor
    · exact hp_gt1
    · ext d
      simp only [DivSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hd_div
        have hd_cases := (Nat.dvd_prime hprime).mp hd_div
        rcases hd_cases with h1 | hp
        · exact Or.inl h1
        · exact Or.inr hp
      · rintro (rfl | rfl)
        · exact one_dvd p
        · exact dvd_rfl
  · rintro ⟨hp_gt1, hdiv_set⟩
    rw [Nat.prime_def_lt']
    refine ⟨hp_gt1, ?_⟩
    intro m hm_gt1 hm_lt_p
    intro hm_div
    have hm_in : m ∈ DivSet p := hm_div
    rw [hdiv_set] at hm_in
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_in
    rcases hm_in with rfl | rfl
    · omega
    · omega

/- =====================================================================
   SECTION VII: THE DUAL-AXIS INCOMMENSURABILITY THEOREMS
   ===================================================================== -/

def manhattan_step : ℝ := 1 + 1
noncomputable def diagonal_step : ℝ := Real.sqrt (1 ^ 2 + 1 ^ 2)

lemma diagonal_eq_sqrt_two : diagonal_step = Real.sqrt 2 := by
  unfold diagonal_step
  ring_nf

theorem manhattan_is_rational : ∃ q : ℚ, (q : ℝ) = manhattan_step := by
  use 2
  unfold manhattan_step
  norm_num

theorem diagonal_is_irrational : Irrational diagonal_step := by
  rw [diagonal_eq_sqrt_two]
  exact irrational_sqrt_two

theorem no_common_rational_measure : ¬ ∃ q : ℚ, (q : ℝ) = diagonal_step := by
  rw [diagonal_eq_sqrt_two]
  intro h
  rcases h with ⟨q, hq⟩
  have h_irrat := irrational_sqrt_two
  exact h_irrat ⟨q, hq⟩

noncomputable def delta_gap : ℝ := manhattan_step - diagonal_step

theorem delta_gap_pos : delta_gap > 0 := by
  unfold delta_gap manhattan_step
  rw [diagonal_eq_sqrt_two]
  have h_sqrt2_lt_two : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
    norm_num
  linarith

theorem two_pi_irrational : Irrational (2 * Real.pi) := by
  have h2 : (2 : ℝ) * Real.pi = ((2 : ℚ) : ℝ) * Real.pi := by push_cast; ring
  rw [h2]
  exact irrational_pi.ratCast_mul (by norm_num)

theorem period_incommensurability :
    ¬ ∃ (m n : ℤ), n ≠ 0 ∧ (m : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) := by
  intro h
  rcases h with ⟨m, n, hn_ne_zero, h_eq⟩
  rw [mul_one] at h_eq
  have h_div : (2 * Real.pi) = ((m : ℚ) / (n : ℚ) : ℚ) := by
    apply_fun (fun x => x / (n : ℝ)) at h_eq
    have hn_real_ne : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn_ne_zero
    rw [mul_div_cancel_left₀ (2 * Real.pi) hn_real_ne] at h_eq
    rw [← h_eq]
    push_cast
    rfl
  have h_rational : ∃ q : ℚ, (q : ℝ) = 2 * Real.pi := by
    use (m : ℚ) / (n : ℚ)
    exact h_div.symm
  rcases h_rational with ⟨q, hq⟩
  exact two_pi_irrational ⟨q, hq⟩

/- Group Inequivalence: (ℝ, +) ≇ U(1), via torsion.
   (ℝ, +) is torsion-free; Circle (≅ U(1)) has a genuine order-2 element (-1).
   No group isomorphism can identify a torsion-free group with one that has torsion. -/

/-- Unbundled form: no bijection ℝ ≃ Circle respects the additive/multiplicative structure
    on both sides. Proved directly from the torsion argument, without going through the
    `Multiplicative`/`MulEquiv` type-tag machinery, to keep the core algebraic argument
    self-contained and low-risk. -/
theorem group_inequivalence
    (f : ℝ ≃ Circle) (hf : ∀ x y : ℝ, f (x + y) = f x * f y) : False := by
  have hf0 : f 0 = 1 := by
    have h : f 0 = f 0 * f 0 := by simpa using hf 0 0
    have heq : f 0 * 1 = f 0 * f 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel heq).symm
  obtain ⟨r, hr⟩ := f.surjective (-1 : Circle)
  have hneg1 : (-1 : Circle) * (-1 : Circle) = 1 := by
    rw [neg_mul_neg, one_mul]
  have h1 : f (r + r) = 1 := by rw [hf, hr, hneg1]
  have h2 : r + r = 0 := f.injective (h1.trans hf0.symm)
  have hr0 : r = 0 := by linarith
  rw [hr0, hf0] at hr
  exact Circle.neg_ne_self 1 hr.symm

/-- Bundled form, matching the paper's `(ℝ, +) ≇ U(1)` notation directly: no `MulEquiv` exists
    between `Multiplicative ℝ` (i.e. (ℝ, +) relabeled with multiplicative notation) and `Circle`.
    Derived as a thin corollary of `group_inequivalence` rather than re-proving the argument. -/
theorem real_not_equiv_circle : ¬ Nonempty (Multiplicative ℝ ≃* Circle) := by
  rintro ⟨g⟩
  apply group_inequivalence (Equiv.trans Multiplicative.ofAdd g.toEquiv)
  intro x y
  change g (Multiplicative.ofAdd (x + y)) = g (Multiplicative.ofAdd x) * g (Multiplicative.ofAdd y)
  have hadd : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  rw [hadd, map_mul]

/- =====================================================================
   SECTION IX: THE TRIADIC STATE MANIFOLD & MEDIATOR DEFECT
   ===================================================================== -/

structure TriadicState (n : ℕ) where
  polar_count : ℝ := (n : ℝ)
  axial_mediator : ℝ := Real.sqrt (n : ℝ)
  boundary_potential : ℝ := (n : ℝ) ^ 2

theorem geometric_mean_bridge (n : ℕ) :
    Real.sqrt ((n : ℝ) * ((n : ℝ) ^ 2)) = (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hn_pos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_cube : (n : ℝ) * ((n : ℝ) ^ 2) = (n : ℝ) ^ 3 := by ring
  rw [h_cube]
  have h_split : (n : ℝ) ^ 3 = ((n : ℝ) ^ 2) * (n : ℝ) := by ring
  rw [h_split, Real.sqrt_mul (sq_nonneg (n : ℝ))]
  rw [Real.sqrt_sq hn_pos]

noncomputable def mediator_defect (n m : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) - Real.sqrt ((n + m : ℕ) : ℝ)

theorem mediator_defect_positive {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    mediator_defect n m > 0 := by
  unfold mediator_defect
  push_cast
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hm_pos
  have h_cross : 0 < 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have h_sq_n : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h_sq_m : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    positivity
  have hsum_pos : 0 < Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) := by
    have h_sq_n : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h_sq_m : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    linarith
  have h_exp : (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ^ 2
      = (n : ℝ) + (m : ℝ) + 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have h1 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
    have h2 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_nonneg
    have expand : (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ^ 2
        = (Real.sqrt (n : ℝ)) ^ 2 + (Real.sqrt (m : ℝ)) ^ 2
          + 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by ring
    rw [expand, h1, h2]
  have h_lt : Real.sqrt ((n : ℝ) + (m : ℝ)) < Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_lt' hsum_pos, h_exp]
    linarith
  linarith

theorem equipartition_fixed_point :
    (Real.cos (Real.pi / 4)) ^ 2 = (1 / 2 : ℝ) ∧
    (Real.sin (Real.pi / 4)) ^ 2 = (1 / 2 : ℝ) := by
  constructor
  · rw [Real.cos_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  · rw [Real.sin_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring

end PrimitiveReflexivity
