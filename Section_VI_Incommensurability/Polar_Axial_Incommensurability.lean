-- Section VI: Polar/Axial Incommensurability
--
-- Mirrors the Manhattan/diagonal incommensurability pattern from Section VII
-- (Foundations.lean, `no_common_rational_measure`), but reconstructed from
-- scratch over Nat/Int arithmetic instead of ℝ, since this directory stays
-- dependency-free (no Mathlib, no `Real`, no `Irrational`).
--
-- The Section VII pattern is: one quantity (manhattan_step) is rational, the
-- other (diagonal_step = √(1²+1²) = √2) is irrational, so no rational ratio
-- relates them. The bare-Lean-compatible version of "√2 is irrational" is
-- the classical statement that no naturals m, n (n ≠ 0) satisfy m² = 2·n² —
-- this needs no real numbers at all, only the classical parity/infinite-
-- descent argument, proved here from first principles.

namespace PrimitiveReflexivity

/-- If `p * p` is even, `p` itself is even. -/
theorem even_of_even_sq {p : Nat} (h : p * p % 2 = 0) : p % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · exact hp
  · exfalso
    have hm := Nat.mul_mod p p 2
    rw [hp] at hm
    simp at hm
    omega

/--
Classical infinite-descent proof that no naturals `p, q` (`q ≠ 0`) satisfy
`p * p = 2 * (q * q)` — the bare-arithmetic form of "√2 is irrational,"
needing no real numbers. Proved by strong induction on `q`: from
`p² = 2q²`, `p` must be even (`p = 2k`), which forces `q² = 2k²` — a
strictly smaller instance of the same equation (`k < q` whenever `q ≠ 0`),
so an infinite descent would be required for a solution to exist, which is
impossible over `Nat`.
-/
theorem no_sqrt2_aux : ∀ q : Nat, ∀ p : Nat, q ≠ 0 → p * p = 2 * (q * q) → False := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro p hq heq
    have hpeven : p * p % 2 = 0 := by omega
    have hp2 : p % 2 = 0 := even_of_even_sq hpeven
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k := ⟨p / 2, by omega⟩
    have e1 : (2 * k) * (2 * k) = 2 * (q * q) := by rw [← hk]; exact heq
    have e2 : (2 * k) * (2 * k) = 4 * (k * k) := by ac_rfl
    have e3 : 4 * (k * k) = 2 * (q * q) := by rw [← e2]; exact e1
    have e4 : q * q = 2 * (k * k) := by omega
    have hk0 : k ≠ 0 := by
      intro hk0'
      rw [hk0'] at e4
      simp at e4
      rcases Nat.mul_eq_zero.mp e4 with h0 | h0 <;> exact hq h0
    have hkq : k < q := by
      rcases Nat.lt_or_ge k q with hlt | hge
      · exact hlt
      · exfalso
        have hsq : q * q ≤ k * k := Nat.mul_le_mul hge hge
        have hkk0 : k * k = 0 := by omega
        rcases Nat.mul_eq_zero.mp hkk0 with h0 | h0 <;> exact hk0 h0
    exact ih k hkq q hk0 e4

/-- No rational number `m / n` (in lowest or any terms) has square 2. -/
theorem no_common_rational_measure_sq2 :
    ¬ ∃ m n : Nat, n ≠ 0 ∧ m * m = 2 * (n * n) := by
  intro ⟨m, n, hn, heq⟩
  exact no_sqrt2_aux n m hn heq

/-- The Polar Clock advances in rational, countable unit steps. -/
def polar_step : Nat := 1

/--
The Axial Clock's closure is fixed, by construction, to the same
algebraic relationship as the diagonal-to-side ratio in Section VII: its
square is exactly double the Polar step's square. This is the discrete,
Mathlib-free analog of `diagonal_step = √(1² + 1²)`.
-/
def PolarAxialCommensurable : Prop :=
  ∃ m n : Nat, n ≠ 0 ∧ m * m = 2 * (n * n * (polar_step * polar_step))

/--
**Polar/Axial Incommensurability.** No finite combination of Polar Clock
ticks (`n`, scaled by `polar_step`) and an integer Axial count (`m`) can
satisfy the Axial closure relationship — the two clocks share no common
rational measure. Mirrors `period_incommensurability` (Section VII) without
depending on Mathlib or real numbers.
-/
theorem polar_axial_incommensurable : ¬ PolarAxialCommensurable := by
  intro ⟨m, n, hn, heq⟩
  simp [polar_step] at heq
  exact no_sqrt2_aux n m hn heq

#print axioms polar_axial_incommensurable
#check @polar_axial_incommensurable

end PrimitiveReflexivity
