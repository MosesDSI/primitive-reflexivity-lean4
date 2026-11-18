/-!
# ZeroInt — zero-axiom arithmetic on `Nat` and `Int`

Pure core Lean 4 (no Mathlib), constructive, zero axioms.

Every core `Int` lemma (`Int.add_comm`, `Int.le_trans`, `Int.mul_pos`, ...) depends on
`propext`, and so do `Nat.mul_assoc` and `Nat.add_mul`. This module rebuilds what the
SimulationExchange modules need from the definitions.

(SimulationExchange's own copy, in namespace `SimulationExchange.ZeroInt`, so the package
stays self-contained. It is identical, apart from the namespace, to
`ProjectionNecessity_bare_lean/ProjectionNecessity/ZeroInt.lean`, namespace
`DSISVerification.ZeroInt`; the two packages do not depend on each other.)

* `Nat`: `add_mul`, `mul_assoc`, `mul_left_comm` by induction, and the tactic `nat_ring`, which
  normalizes both sides of a `Nat` equation with `conv` + `simp only` over axiom-free lemmas.
* `Int`: every integer is `mk p n = Int.subNatNat p n` ("p minus n"). Addition, negation,
  subtraction, multiplication, `≤` and `<` on `mk` are computed on the `Nat` pair
  (`mk_add`, `mk_neg`, `mk_sub`, `mk_mul`, `mk_le`, `mk_lt`), so an `Int` statement becomes a
  `Nat` statement. From these come the commutative-ring and order laws used downstream.

Closing a goal with `simp` uses `propext`; rewriting with `simp only` / `rw` and closing by `rfl`
does not. That is why the normalizing tactics normalize each side in `conv` and let the
final `rfl` close the goal.
-/

set_option genInjectivity false

namespace SimulationExchange.ZeroInt

/-! ## `Nat` -/

theorem nat_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm, Nat.left_distrib, Nat.mul_comm c a, Nat.mul_comm c b]

theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.left_distrib, ih]

theorem nat_mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← nat_mul_assoc, Nat.mul_comm a b, nat_mul_assoc]

/-- Normalize both sides of a `Nat` equation (commutative semiring) and close by `rfl`. -/
macro "nat_ring" : tactic => `(tactic| (
  (try conv => lhs; simp only [Nat.left_distrib, nat_add_mul, nat_mul_assoc, Nat.mul_comm,
    nat_mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_one, Nat.one_mul,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.succ_eq_add_one, Nat.mul_two,
    Nat.two_mul])
  (try conv => rhs; simp only [Nat.left_distrib, nat_add_mul, nat_mul_assoc, Nat.mul_comm,
    nat_mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_one, Nat.one_mul,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.succ_eq_add_one, Nat.mul_two,
    Nat.two_mul])))

/-- Left cancellation for `≤` (core's `Nat.le_of_add_le_add_left` uses `propext`). -/
theorem nat_le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c :=
  Nat.le_of_lt_succ (Nat.lt_of_add_lt_add_left (Nat.lt_succ_of_le h : a + b < a + (c + 1)))

/-- `(n + k) - (m + k) = n - m`. -/
theorem sub_shift (n m : Nat) : ∀ k : Nat, (n + k) - (m + k) = n - m
  | 0 => rfl
  | k + 1 => (Nat.succ_sub_succ (n + k) (m + k)).trans (sub_shift n m k)

/-! ## `Int` as a difference of naturals -/

/-- `mk p n` is the integer `p − n`. -/
def mk (p n : Nat) : Int := Int.subNatNat p n

theorem mk_shift (p n k : Nat) : mk (p + k) (n + k) = mk p n := by
  unfold mk Int.subNatNat
  rw [sub_shift n p k, sub_shift p n k]

/-- Two pairs name the same integer when their cross sums agree. -/
theorem mk_eq_of {a b c d : Nat} (h : a + d = c + b) : mk a b = mk c d :=
  calc mk a b = mk (a + d) (b + d) := (mk_shift a b d).symm
    _ = mk (c + b) (b + d) := by rw [h]
    _ = mk (c + b) (d + b) := by rw [Nat.add_comm b d]
    _ = mk c d := mk_shift c d b

theorem mk_zero_left (k : Nat) : mk k 0 = (k : Int) :=
  Int.subNatNat_of_sub_eq_zero (Nat.zero_sub k)

theorem mk_succ_right (k : Nat) : mk 0 (k + 1) = Int.negSucc k :=
  Int.subNatNat_of_sub_eq_succ rfl

theorem mk_of_le {a b : Nat} (k : Nat) (h : b + k = a) : mk a b = (k : Int) :=
  (mk_eq_of (show a + 0 = k + b from h ▸ Nat.add_comm b k)).trans (mk_zero_left k)

theorem mk_of_lt {a b : Nat} (k : Nat) (h : a + (k + 1) = b) : mk a b = Int.negSucc k :=
  (mk_eq_of (show a + (k + 1) = 0 + b from h.trans (Nat.zero_add b).symm)).trans (mk_succ_right k)

/-- Every pair is in one of the two canonical shapes. -/
theorem pair_cases (a b : Nat) : (∃ k, b + k = a) ∨ (∃ k, a + (k + 1) = b) := by
  rcases Nat.lt_or_ge a b with h | h
  · obtain ⟨k, hk⟩ := Nat.le.dest h
    exact Or.inr ⟨k, (Nat.add_assoc a 1 k).symm.trans
      ((congrArg (· + k) (rfl : a + 1 = a.succ)).trans hk) |>.symm ▸ by
        rw [Nat.add_comm k 1, ← Nat.add_assoc]⟩
  · exact Or.inl (Nat.le.dest h)

/-- Every integer is some `mk p n`. -/
theorem exists_mk (x : Int) : ∃ p n, x = mk p n := by
  cases x with
  | ofNat k => exact ⟨k, 0, (mk_zero_left k).symm⟩
  | negSucc k => exact ⟨0, k + 1, (mk_succ_right k).symm⟩

theorem mk_add (a b c d : Nat) : mk a b + mk c d = mk (a + c) (b + d) := by
  rcases pair_cases a b with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rcases pair_cases c d with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [mk_of_le k rfl, mk_of_le l rfl]
    rw [Int.ofNat_add_ofNat, ← mk_zero_left]
    exact mk_eq_of (by nat_ring)
  · rw [mk_of_le k rfl, mk_of_lt l rfl]
    rw [Int.ofNat_add_negSucc]
    exact mk_eq_of (by nat_ring)
  · rw [mk_of_lt k rfl, mk_of_le l rfl]
    rw [Int.negSucc_add_ofNat]
    exact mk_eq_of (by nat_ring)
  · rw [mk_of_lt k rfl, mk_of_lt l rfl, Int.negSucc_add_negSucc, ← mk_succ_right]
    exact mk_eq_of (by nat_ring)

theorem mk_neg (a b : Nat) : -mk a b = mk b a := by
  rcases pair_cases a b with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [mk_of_le k rfl]
    cases k with
    | zero =>
      rw [Int.neg_ofNat_zero, show (0 : Int) = mk 0 0 from rfl]
      exact mk_eq_of (by nat_ring)
    | succ k =>
      rw [Int.neg_ofNat_succ, ← mk_succ_right]
      exact mk_eq_of (by nat_ring)
  · rw [mk_of_lt k rfl, Int.neg_negSucc, ← mk_zero_left]
    exact mk_eq_of (by nat_ring)

theorem mk_sub (a b c d : Nat) : mk a b - mk c d = mk (a + d) (b + c) := by
  rw [Int.sub_eq_add_neg, mk_neg, mk_add]

theorem negOfNat_eq_mk (k : Nat) : -(k : Int) = mk 0 k := by
  rw [← mk_zero_left, mk_neg]

theorem mk_mul (a b c d : Nat) : mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := by
  rcases pair_cases a b with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rcases pair_cases c d with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [mk_of_le k rfl, mk_of_le l rfl]
    rw [Int.ofNat_mul_ofNat, ← mk_zero_left]
    exact mk_eq_of (by nat_ring)
  · rw [mk_of_le k rfl, mk_of_lt l rfl]
    rw [Int.ofNat_mul_negSucc, negOfNat_eq_mk]
    exact mk_eq_of (by nat_ring)
  · rw [mk_of_lt k rfl, mk_of_le l rfl]
    rw [Int.negSucc_mul_ofNat, negOfNat_eq_mk]
    exact mk_eq_of (by nat_ring)
  · rw [mk_of_lt k rfl, mk_of_lt l rfl, Int.negSucc_mul_negSucc, Int.ofNat_mul_ofNat,
      ← mk_zero_left]
    exact mk_eq_of (by nat_ring)

/-- `NonNeg (mk p n)` exactly when `n ≤ p`. -/
theorem nonNeg_mk {p n : Nat} : Int.NonNeg (mk p n) ↔ n ≤ p := by
  constructor
  · intro h
    rcases pair_cases p n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact hk ▸ Nat.le_add_right n k
    · rw [mk_of_lt k hk] at h; cases h
  · intro h
    obtain ⟨k, hk⟩ := Nat.le.dest h
    rw [mk_of_le k hk]; exact Int.NonNeg.mk k

theorem mk_le {a b c d : Nat} : mk a b ≤ mk c d ↔ a + d ≤ c + b := by
  show Int.NonNeg (mk c d - mk a b) ↔ _
  rw [mk_sub, Nat.add_comm a d]
  exact nonNeg_mk

theorem mk_lt {a b c d : Nat} : mk a b < mk c d ↔ a + d < c + b := by
  show mk a b + 1 ≤ mk c d ↔ _
  rw [show (1 : Int) = mk 1 0 from rfl, mk_add, Nat.add_zero]
  have e : a + 1 + d = (a + d) + 1 := by nat_ring
  constructor
  · intro h; have h' := mk_le.1 h; rw [e] at h'; exact h'
  · intro h; apply mk_le.2; rw [e]; exact h

theorem mk_eq {a b c d : Nat} : mk a b = mk c d ↔ a + d = c + b := by
  constructor
  · intro h
    have h1 : mk a b ≤ mk c d := by rw [← h]; exact mk_le.2 (Nat.le_refl _)
    have h2 : mk c d ≤ mk a b := by rw [h]; exact mk_le.2 (Nat.le_refl _)
    exact Nat.le_antisymm (mk_le.1 h1) (mk_le.1 h2)
  · exact mk_eq_of

/-! ## Ring laws for `Int`, axiom-free -/

theorem add_comm (x y : Int) : x + y = y + x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_add, mk_add]; exact mk_eq_of (by nat_ring)

theorem add_assoc (x y z : Int) : x + y + z = x + (y + z) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  rw [mk_add, mk_add, mk_add, mk_add]; exact mk_eq_of (by nat_ring)

theorem add_left_comm (x y z : Int) : x + (y + z) = y + (x + z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

theorem mul_comm (x y : Int) : x * y = y * x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_mul, mk_mul]; exact mk_eq_of (by nat_ring)

theorem mul_assoc (x y z : Int) : x * y * z = x * (y * z) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  rw [mk_mul, mk_mul, mk_mul, mk_mul]; exact mk_eq_of (by nat_ring)

theorem mul_left_comm (x y z : Int) : x * (y * z) = y * (x * z) := by
  rw [← mul_assoc, mul_comm x y, mul_assoc]

theorem mul_add (x y z : Int) : x * (y + z) = x * y + x * z := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  rw [mk_add, mk_mul, mk_mul, mk_mul, mk_add]; exact mk_eq_of (by nat_ring)

theorem add_mul (x y z : Int) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, mul_add, mul_comm z x, mul_comm z y]

theorem neg_add (x y : Int) : -(x + y) = -x + -y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_add, mk_neg, mk_neg, mk_neg, mk_add]

theorem mul_neg (x y : Int) : x * -y = -(x * y) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_neg, mk_mul, mk_mul, mk_neg]

theorem neg_mul (x y : Int) : -x * y = -(x * y) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem zero_add (x : Int) : 0 + x = x := by
  rw [add_comm]; exact Int.add_zero x

theorem zero_mul (x : Int) : 0 * x = 0 := by
  rw [mul_comm]; exact Int.mul_zero x

theorem mul_one (x : Int) : x * 1 = x := by
  rw [mul_comm]; exact Int.one_mul x

theorem add_neg_cancel (x : Int) : x + -x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rw [mk_neg, mk_add, show (0 : Int) = mk 0 0 from rfl]; exact mk_eq_of (by nat_ring)

/-- Normalize both sides of an `Int` equation without subtraction cancellation (commutative
ring laws, negation pushed onto monomials) and close by `rfl`. -/
macro "int_ring" : tactic => `(tactic| (
  (try conv => lhs; simp only [Int.sub_eq_add_neg, mul_add, add_mul, neg_add, mul_neg, neg_mul,
    Int.neg_neg, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm,
    mul_one, Int.one_mul, Int.mul_zero, zero_mul, Int.add_zero, zero_add, Int.neg_zero])
  (try conv => rhs; simp only [Int.sub_eq_add_neg, mul_add, add_mul, neg_add, mul_neg, neg_mul,
    Int.neg_neg, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm,
    mul_one, Int.one_mul, Int.mul_zero, zero_mul, Int.add_zero, zero_add, Int.neg_zero])))

/-! ## Order -/

theorem le_iff_nonNeg (x y : Int) : x ≤ y ↔ Int.NonNeg (y - x) := Iff.rfl

theorem le_refl (x : Int) : x ≤ x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; exact mk_le.2 (Nat.le_refl _)

theorem le_trans {x y z : Int} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  have h := Nat.add_le_add (mk_le.1 h₁) (mk_le.1 h₂)
  refine mk_le.2 (nat_le_of_add_le_add_left (a := c + d) ?_)
  exact Nat.le_trans (Nat.le_of_eq (by nat_ring)) (Nat.le_trans h (Nat.le_of_eq (by nat_ring)))

theorem lt_irrefl (x : Int) : ¬ x < x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; exact fun h => Nat.lt_irrefl _ (mk_lt.1 h)

theorem lt_of_lt_of_le {x y z : Int} (h₁ : x < y) (h₂ : y ≤ z) : x < z := le_trans h₁ h₂

theorem lt_or_le (x y : Int) : x < y ∨ y ≤ x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rcases Nat.lt_or_ge (a + d) (c + b) with h | h
  · exact Or.inl (mk_lt.2 h)
  · exact Or.inr (mk_le.2 h)

theorem not_le_of_lt {x y : Int} (h : x < y) : ¬ y ≤ x :=
  fun h' => lt_irrefl x (lt_of_lt_of_le h h')

theorem lt_of_le_of_ne {x y : Int} (h : x ≤ y) (hne : x ≠ y) : x < y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  exact mk_lt.2 (Nat.lt_of_le_of_ne (mk_le.1 h) (fun e => hne (mk_eq_of e)))

/-- Multiplying by a positive constant is injective. -/
theorem eq_of_mul_eq_mul_left {k : Nat} (hk : 0 < k) {x y : Int}
    (h : (k : Int) * x = (k : Int) * y) : x = y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [← mk_zero_left, mk_mul, mk_mul] at h
  have e := mk_eq.1 h
  refine mk_eq_of (Nat.eq_of_mul_eq_mul_left hk ?_)
  rw [Nat.left_distrib, Nat.left_distrib]
  repeat (first | rw [Nat.zero_mul] at e | rw [Nat.add_zero] at e)
  exact e

/-! ## Helpers for transferred proofs -/

/-- Cancel a common summand `K` from both sides of a `Nat` inequality whose sides are given
up to a `nat_ring` identity. -/
theorem nat_le_of_sum {A B C D K : Nat} (h : A ≤ B) (hA : A = K + C) (hB : B = K + D) : C ≤ D :=
  nat_le_of_add_le_add_left (a := K) (hA ▸ hB ▸ h)

/-- Rewrite every `+`, `-`, `*`, unary `-` between `mk` terms into a single `mk`. -/
macro "int_transfer" : tactic => `(tactic|
  repeat (first | rw [mk_add] | rw [mk_sub] | rw [mk_mul] | rw [mk_neg]))

theorem two_mul (x : Int) : 2 * x = x + x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rw [show (2 : Int) = mk 2 0 from rfl, mk_mul, mk_add]; exact mk_eq_of (by nat_ring)

/-! ## Cancellation identities (each proved through the `Nat` transfer) -/

theorem sub_self (x : Int) : x - x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rw [mk_sub, show (0 : Int) = mk 0 0 from rfl]; exact mk_eq_of (by nat_ring)

theorem neg_sub (x y : Int) : -(x - y) = y - x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_sub, mk_neg, mk_sub]; exact mk_eq_of (by nat_ring)

theorem add_add_sub (x y : Int) : (x + y) + (x - y) = x + x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  int_transfer; exact mk_eq_of (by nat_ring)

theorem add_sub_sub (x y : Int) : (x + y) - (x - y) = y + y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x; obtain ⟨c, d, rfl⟩ := exists_mk y
  int_transfer; exact mk_eq_of (by nat_ring)

theorem sub_neg_self (x : Int) : x - -x = 2 * x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rw [two_mul]; int_transfer

/-- An integer equal to its own negation is 0. -/
theorem eq_zero_of_eq_neg {x : Int} (h : x = -x) : x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rw [mk_neg] at h
  have e : a + a = b + b := mk_eq.1 h
  have e2 : 2 * a = 2 * b := by rw [Nat.two_mul, Nat.two_mul]; exact e
  have hab : a = b := Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 1) e2
  subst hab
  rw [show (0 : Int) = mk 0 0 from rfl]; exact mk_eq_of (by nat_ring)

/-- An integer is 0 exactly when its pair is balanced. -/
theorem mk_eq_zero {a b : Nat} (h : mk a b = 0) : a = b := by
  have e : a + 0 = 0 + b := mk_eq.1 (h.trans (show (0 : Int) = mk 0 0 from rfl))
  rw [Nat.add_zero, Nat.zero_add] at e; exact e

/-- Cancel a common summand `K` from both sides of a `Nat` equation. -/
theorem nat_eq_of_sum {A B C D K : Nat} (h : A = B) (hA : A = K + C) (hB : B = K + D) : C = D :=
  have e := hA.symm.trans (h.trans hB)
  Nat.le_antisymm (nat_le_of_add_le_add_left (Nat.le_of_eq e))
    (nat_le_of_add_le_add_left (Nat.le_of_eq e.symm))

/-- `Fin` numerals without core's `Fin.instOfNat`, whose `NeZero`-based proof term depends on
`propext`. Scoped: active only where `SimulationExchange.ZeroInt` is opened. It agrees with core
on every in-range literal `k < n + 1`. -/
scoped instance (priority := high) finOfNat {n k : Nat} : OfNat (Fin (n + 1)) k :=
  ⟨if h : k < n + 1 then ⟨k, h⟩ else ⟨0, Nat.zero_lt_succ n⟩⟩

end SimulationExchange.ZeroInt
