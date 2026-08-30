-- Section VI/VIII: Axial Divergence Theorem
--
-- Ties `PhaseDriftMatch` (R3_bare_lean/Section_VI_dual_clock.lean) directly
-- to the Polar/Axial incommensurability result (Polar_Axial_Incommensurability.lean
-- in this folder) — not just thematically, but as an actual proof term: this
-- file shows PhaseDriftMatch's own certified reachable phase can never
-- satisfy the √2-closure relationship with the Polar clock, for any fixed
-- natural per-tick Axial rotation.
--
-- Definitions restated from the two source files above for standalone
-- `lean` compilation, per this repo's convention (no cross-file imports,
-- no lake wiring, no Mathlib).

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

namespace PrimitiveReflexivity

structure BifurcatedState (N : Type) (Phase : Type) where
  polar_clock : Nat
  axial_clock : Phase

class AxialRotation (Phase : Type) where
  rotate_step : Phase → Phase

def PhaseDriftMatch {N : Type} {Phase : Type} [r : AxialRotation Phase]
    (state : BifurcatedState N Phase) (target_phase : Phase) : Prop :=
  iterate r.rotate_step state.polar_clock state.axial_clock = target_phase

-- From Polar_Axial_Incommensurability.lean: the bare-arithmetic proof that
-- no naturals p, q (q ≠ 0) satisfy p * p = 2 * (q * q).

theorem even_of_even_sq {p : Nat} (h : p * p % 2 = 0) : p % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · exact hp
  · exfalso
    have hm := Nat.mul_mod p p 2
    rw [hp] at hm
    simp at hm
    omega

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

-- The connecting result.

/-- A fixed-increment Axial rotation over `Nat`: each tick adds a constant
    `c`. Passed explicitly rather than registered via `instance` (this file
    only ever needs one concrete rotation at a time, chosen by the caller —
    marked `instance_reducible` purely to silence the class-reducibility
    linter, not for typeclass search). -/
@[instance_reducible]
def constStepInstance (c : Nat) : AxialRotation Nat := ⟨fun x => x + c⟩

theorem iterate_add_const (c n start : Nat) :
    iterate (fun x => x + c) n start = start + n * c := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    show (fun x => x + c) (iterate (fun x => x + c) n start) = start + (n + 1) * c
    rw [ih, Nat.succ_mul]
    simp only []
    omega

/-- `PhaseDriftMatch` certifies that this Axial clock, starting at `0`,
    deterministically reaches phase `n * c` after `n` Polar ticks. This is
    the non-vacuous half: a real, specific value is reached, not an
    unconstrained existential. -/
theorem const_step_reaches (c n : Nat) :
    @PhaseDriftMatch Unit Nat (constStepInstance c) (BifurcatedState.mk n 0) (n * c) := by
  show iterate (fun x => x + c) n 0 = n * c
  rw [iterate_add_const]
  omega

/-- That certified reached phase can never satisfy the √2-closure
    relationship with the Polar clock, for any `n ≠ 0` — direct instance of
    `no_sqrt2_aux` with `p := n * c`, `q := n`. -/
theorem sqrt2_gap_unreachable (c n : Nat) (hn : n ≠ 0) :
    (n * c) * (n * c) ≠ 2 * (n * n) := by
  intro heq
  exact no_sqrt2_aux n (n * c) hn heq

/--
**Axial Divergence Theorem.** For any fixed natural per-tick Axial rotation
`c`, and any positive Polar tick count `n`: `PhaseDriftMatch` certifies that
the Axial clock deterministically reaches phase `n * c` after `n` Polar
ticks — and that exact certified phase can never satisfy the √2-closure
relationship with the Polar clock, for any choice of `c` whatsoever.

This is the actual structural link between `PhaseDriftMatch` and the
Polar/Axial incommensurability result: `PhaseDriftMatch` supplies the real,
non-vacuous reached value, and `no_sqrt2_aux` (the same lemma behind
`polar_axial_incommensurable`) is what rules out that value ever closing
the diagonal gap — not two independent results sitting near each other.
-/
theorem axial_clock_never_closes_the_diagonal_gap (c n : Nat) (hn : n ≠ 0) :
    @PhaseDriftMatch Unit Nat (constStepInstance c) (BifurcatedState.mk n 0) (n * c) ∧
    (n * c) * (n * c) ≠ 2 * (n * n) :=
  ⟨const_step_reaches c n, sqrt2_gap_unreachable c n hn⟩

#print axioms axial_clock_never_closes_the_diagonal_gap
#check @axial_clock_never_closes_the_diagonal_gap

-- Sanity: the "reached" half is non-vacuous -- a concrete instance really
-- does reach the claimed value, confirming this isn't an always-false
-- vacuous statement dressed up as a theorem.
example : @PhaseDriftMatch Unit Nat (constStepInstance 3) (BifurcatedState.mk 2 0) 6 :=
  const_step_reaches 3 2

end PrimitiveReflexivity
