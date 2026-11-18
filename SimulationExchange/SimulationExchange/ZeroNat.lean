import SimulationExchange.ZeroInt

/-!
# ZeroNat — zero-axiom order lemmas on `Nat`

Core's `Nat.mul_self_le_mul_self`, `Nat.mul_self_lt_mul_self_iff`,
`Nat.mul_lt_mul_of_pos_right`, `Nat.mul_pos` and `Nat.lt_of_mul_lt_mul_right`
are what SimulationExchange's descent used; several carry `propext`. This
module proves the needed facts from the definitions, using only ZeroInt's
proved lemmas by name (never its macros).

SimulationExchange's own copy: the same proofs as
`ProjectionNecessity_bare_lean` Steps 7a and 7c, restated here so that the two
packages stay independent.

Hygiene: no `simp`, `omega`, `decide`, `by_cases`, `grind`; no written Nat
subtraction. Target: zero axioms for every declaration.
-/


set_option genInjectivity false

namespace SimulationExchange.ZeroNat

open SimulationExchange.ZeroInt (nat_add_mul nat_mul_assoc nat_mul_left_comm)

/-- Squaring is monotone: `a ≤ b → a * a ≤ b * b`. Write `b = a + k`; then
`b * b = a * a + (a * k + k * (a + k))`. -/
theorem mul_self_le_mul_self {a b : Nat} (h : a ≤ b) : a * a ≤ b * b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  have e : (a + k) * (a + k) = a * a + (a * k + k * (a + k)) :=
    Eq.trans (nat_add_mul a k (a + k))
      (Eq.trans (congrArg (fun t => t + k * (a + k)) (Nat.left_distrib a a k))
        (Nat.add_assoc (a * a) (a * k) (k * (a + k))))
  exact Nat.le_trans (Nat.le_add_right (a * a) (a * k + k * (a + k)))
    (Nat.le_of_eq (Eq.symm e))

/-- Squares compare like their roots: `a * a < b * b → a < b`. -/
theorem lt_of_mul_self_lt_mul_self {a b : Nat} (h : a * a < b * b) : a < b :=
  match Nat.lt_or_ge a b with
  | Or.inl hlt => hlt
  | Or.inr hge =>
    absurd (Nat.lt_of_lt_of_le h (mul_self_le_mul_self hge)) (Nat.lt_irrefl (a * a))

/-- Multiplying a strict inequality by a positive number. -/
theorem mul_lt_mul_right_of_pos {a b c : Nat} (h : a < b) (hc : 0 < c) :
    a * c < b * c := by
  obtain ⟨k, hk⟩ := Nat.le.dest (h : a + 1 ≤ b)
  subst hk
  have e : (a + 1 + k) * c = a * c + c + k * c :=
    Eq.trans (nat_add_mul (a + 1) k c)
      (congrArg (fun t => t + k * c)
        (Eq.trans (nat_add_mul a 1 c) (congrArg (fun t => a * c + t) (Nat.one_mul c))))
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hc (a * c) : a * c + 0 < a * c + c)
    (Nat.le_trans (Nat.le_add_right (a * c + c) (k * c)) (Nat.le_of_eq (Eq.symm e)))

/-- A product of positive numbers is positive. -/
theorem mul_pos' {a b : Nat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  Nat.lt_of_le_of_lt (Nat.le_of_eq (Eq.symm (Nat.zero_mul b)))
    (mul_lt_mul_right_of_pos ha hb)

/-- Squaring is strictly monotone. -/
theorem mul_self_lt_of_lt {a b : Nat} (h : a < b) : a * a < b * b := by
  have h₁ : a * a ≤ a * b := by
    obtain ⟨k, hk⟩ := Nat.le.dest (Nat.le_of_lt h)
    subst hk
    exact Nat.le_trans (Nat.le_add_right (a * a) (a * k))
      (Nat.le_of_eq (Eq.symm (Nat.left_distrib a a k)))
  exact Nat.lt_of_le_of_lt h₁
    (mul_lt_mul_right_of_pos h (Nat.lt_of_le_of_lt (Nat.zero_le a) h))

/-- `(x y)² = x² y²`. -/
theorem mul_mul_self (x y : Nat) : (x * y) * (x * y) = x * x * (y * y) :=
  Eq.trans (nat_mul_assoc x y (x * y))
    (Eq.trans (congrArg (fun t => x * t) (nat_mul_left_comm y x y))
      (Eq.symm (nat_mul_assoc x x (y * y))))

/-- `m * m = 0 → m = 0`: a successor squared is a successor. -/
theorem mul_self_eq_zero : ∀ {m : Nat}, m * m = 0 → m = 0
  | 0, _ => rfl
  | _ + 1, h => Nat.noConfusion h

end SimulationExchange.ZeroNat
