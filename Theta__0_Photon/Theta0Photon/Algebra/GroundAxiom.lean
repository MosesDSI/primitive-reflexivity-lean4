import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Rat.Sqrt

/-!
# THE GROUND AXIOM: TRIADIC BASELINE IRREDUCIBILITY

The root algebraic obstruction driving the Coheron-SCC framework: `X² - n` is
irreducible over `ℚ` for any non-square natural `n`.

This file exposes the "no rational root" fact
(`triadic_no_rational_root`) as its own reusable lemma, since the next phase
of this project (`FieldTower.lean`) needs it directly (to identify a minimal
polynomial), not only as a step buried inside the irreducibility proof.
`triadic_ground_irreducible` is then just the standard "no roots at degree 2"
corollary of it.
-/

open Polynomial

variable (n : ℕ)

/-- No rational number squares to a non-square natural `n`. This is the
computational heart of `triadic_ground_irreducible` below, exposed on its own
because `FieldTower.lean` needs the "no rational root of `X² - n`" fact
directly, to identify `minpoly ℚ (Real.sqrt n)`. -/
theorem triadic_no_rational_root (hn : ¬ ∃ k : ℕ, k * k = n) (r : ℚ) :
    eval r (X ^ 2 - C (n : ℚ)) ≠ 0 := by
  intro h_eval
  rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h_eval
  have h_mul : r * r = (n : ℚ) := by rw [← sq]; exact h_eval
  have h_sqrt : Rat.sqrt (n : ℚ) * Rat.sqrt (n : ℚ) = (n : ℚ) :=
    (Rat.exists_mul_self (n : ℚ)).mp ⟨r, h_mul⟩
  rw [Rat.sqrt_natCast] at h_sqrt
  have h_nat : Nat.sqrt n * Nat.sqrt n = n := by exact_mod_cast h_sqrt
  exact hn ⟨Nat.sqrt n, h_nat⟩

/--
Axiom / Proposition 1.1:
For any non-square natural number, the polynomial X² - n is irreducible over ℚ.
-/
theorem triadic_ground_irreducible (hn : ¬ ∃ k : ℕ, k * k = n) :
    Irreducible (X ^ 2 - C (n : ℚ)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    omega
  · intro r hr
    exact triadic_no_rational_root n hn r hr
