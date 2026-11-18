/-
  Projection Necessity, Step 7c: the descent.

  Bare Lean 4. Imports Step 7b (with Steps 7a, 6, 5, 3 and ZeroInt).
  Nothing from `SimulationExchange`, `Real` or `Rat`.

  Hygiene, as in Steps 1–7b: no `simp`, `omega`, `decide`, `by_cases` or
  `grind`, and none of ZeroInt's macros; ZeroInt's proved lemmas are used
  by name. No `Nat` subtraction: differences are introduced as witnesses
  (`r * n + n' = j`). Strong induction is done by hand, as ordinary
  induction on a bound. Target: zero axioms for every declaration.

  Main result.

  * `no_square_multiple`: if `d` is not a perfect square and `n > 0`,
    then `j * j ≠ n * n * d` for every `j`. (√d is not a ratio `j / n`.)
  * `nonSquare_tick`: `NonSquare d → 0 < n → NonSquare (4 * n * n * d)`,
    the special case `n ↦ 2n`. This discharges the last hypothesis of
    Steps 7a and 7b.

  Proof of `no_square_multiple`, by descent on `n` (no primes, no gcd).
  Let `r = ⌊√d⌋`, so `r² < d < (r+1)²` because `d` is not a square.
  Suppose `j² = n²d` with `n > 0`. Then `rn < j < (r+1)n`, so
  `n' := j − rn` satisfies `0 < n' < n`. Put `j' := dn − rj` (positive,
  since `(rj)² < (dn)²`). Two cross relations hold,
      `j'·n = n'·j`   and   `j'·j = n'·(dn)`,
  each by cancelling a common summand (`ZeroInt.nat_eq_of_sum`), and
  together they give `n·j'² = n·(n'²d)`, so `j'² = n'²d`: a smaller
  solution. A strictly decreasing sequence of positive `n` cannot exist.

  Corollaries: the flip-floor identity and the walker hands of Step 7b,
  now from `NonSquare d` and `0 < n` alone.
-/

import ProjectionNecessity.Step7b_ParityBookkeeping

set_option genInjectivity false

namespace PrimitiveReflexivity.ProjectionNecessity

open DSISVerification.ZeroInt (nat_add_mul nat_mul_assoc nat_mul_left_comm nat_eq_of_sum)

/-! ## Order and products on `Nat` -/

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

/-- `(x y)² = x² y²`, rearranged with ZeroInt's associativity lemmas. -/
theorem mul_mul_self (x y : Nat) : (x * y) * (x * y) = x * x * (y * y) :=
  Eq.trans (nat_mul_assoc x y (x * y))
    (Eq.trans (congrArg (fun t => x * t) (nat_mul_left_comm y x y))
      (Eq.symm (nat_mul_assoc x x (y * y))))

/-! ## The integer square root -/

/-- **Every `X` has an integer square root:** `r² ≤ X < (r+1)²`. -/
theorem exists_floor_sqrt : ∀ X : Nat, ∃ r : Nat, r * r ≤ X ∧ X < (r + 1) * (r + 1)
  | 0 => ⟨0, Nat.le_refl 0, Nat.zero_lt_one⟩
  | X + 1 => by
    obtain ⟨r, h₁, h₂⟩ := exists_floor_sqrt X
    cases Nat.lt_or_eq_of_le (h₂ : X + 1 ≤ (r + 1) * (r + 1)) with
    | inl hlt => exact ⟨r, Nat.le_succ_of_le h₁, hlt⟩
    | inr heq =>
      exact ⟨r + 1, Nat.le_of_eq (Eq.symm heq),
        Nat.lt_of_le_of_lt (Nat.le_of_eq heq) (mul_self_lt_of_lt (Nat.lt_succ_self (r + 1)))⟩

/-! ## One step of descent -/

/-- **One descent step.** If `d` is not a square, `n > 0` and `j² = n²d`,
there is a smaller positive `n'` with some `j'² = n'²d`. -/
theorem descent_step {d n j : Nat} (hd : NonSquare d) (hn : 0 < n)
    (hj : j * j = n * n * d) :
    ∃ n' j' : Nat, 0 < n' ∧ n' < n ∧ j' * j' = n' * n' * d := by
  -- `r = ⌊√d⌋`, strictly below `√d` because `d` is not a square.
  obtain ⟨r, hr₁, hr₂⟩ := exists_floor_sqrt d
  have hr : r * r < d := Nat.lt_of_le_of_ne hr₁ (hd r)
  have hd₀ : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le (r * r)) hr
  have hnn : 0 < n * n := mul_pos' hn hn
  have hjj : 0 < j * j :=
    Nat.lt_of_lt_of_le (mul_pos' hnn hd₀) (Nat.le_of_eq (Eq.symm hj))
  have hjd : j * j = d * (n * n) := Eq.trans hj (Nat.mul_comm (n * n) d)
  -- `r n < j`
  have hlo : r * n < j :=
    lt_of_mul_self_lt_mul_self
      (Nat.lt_of_le_of_lt (Nat.le_of_eq (mul_mul_self r n))
        (Nat.lt_of_lt_of_le (mul_lt_mul_right_of_pos hr hnn) (Nat.le_of_eq (Eq.symm hjd))))
  -- `j < (r + 1) n`
  have hhi : j < (r + 1) * n :=
    lt_of_mul_self_lt_mul_self
      (Nat.lt_of_le_of_lt (Nat.le_of_eq hjd)
        (Nat.lt_of_lt_of_le (mul_lt_mul_right_of_pos hr₂ hnn)
          (Nat.le_of_eq (Eq.symm (mul_mul_self (r + 1) n)))))
  -- `n' = j − r n`, as a witness
  obtain ⟨n', hA⟩ := Nat.le.dest (Nat.le_of_lt hlo)
  have hn'pos : 0 < n' :=
    Nat.lt_of_add_lt_add_left
      (Nat.lt_of_lt_of_le hlo (Nat.le_of_eq (Eq.symm hA)) : r * n + 0 < r * n + n')
  have e_r1n : (r + 1) * n = r * n + n :=
    Eq.trans (nat_add_mul r 1 n) (congrArg (fun t => r * n + t) (Nat.one_mul n))
  have hn'lt : n' < n :=
    Nat.lt_of_add_lt_add_left
      (Nat.lt_of_le_of_lt (Nat.le_of_eq hA)
        (Nat.lt_of_lt_of_le hhi (Nat.le_of_eq e_r1n)) : r * n + n' < r * n + n)
  -- `r j < d n`
  have e_dn : d * (j * j) = (d * n) * (d * n) :=
    Eq.trans (congrArg (fun t => d * t) hjd)
      (Eq.trans (Eq.symm (nat_mul_assoc d d (n * n))) (Eq.symm (mul_mul_self d n)))
  have hrj : r * j < d * n :=
    lt_of_mul_self_lt_mul_self
      (Nat.lt_of_le_of_lt (Nat.le_of_eq (mul_mul_self r j))
        (Nat.lt_of_lt_of_le (mul_lt_mul_right_of_pos hr hjj) (Nat.le_of_eq e_dn)))
  -- `j' = d n − r j`, as a witness
  obtain ⟨j', hB⟩ := Nat.le.dest (Nat.le_of_lt hrj)
  -- Cross relation 1: `j' n = n' j`.
  have e₁ : d * n * n = n * n * d :=
    Eq.trans (nat_mul_assoc d n n) (Nat.mul_comm d (n * n))
  have e₂ : r * j * n = r * n * j :=
    Eq.trans (nat_mul_assoc r j n)
      (Eq.trans (congrArg (fun t => r * t) (Nat.mul_comm j n))
        (Eq.symm (nat_mul_assoc r n j)))
  have hD : j' * n = n' * j :=
    nat_eq_of_sum (K := r * n * j)
      (Eq.trans e₁ (Eq.symm hj) : d * n * n = j * j)
      (Eq.trans (congrArg (fun t => t * n) (Eq.symm hB))
        (Eq.trans (nat_add_mul (r * j) j' n) (congrArg (fun t => t + j' * n) e₂)))
      (Eq.trans (congrArg (fun t => t * j) (Eq.symm hA)) (nat_add_mul (r * n) n' j))
  -- Cross relation 2: `j' j = n' (d n)`.
  have e₃ : r * j * j = r * n * (d * n) :=
    Eq.trans (nat_mul_assoc r j j)
      (Eq.trans
        (congrArg (fun t => r * t)
          (Eq.trans hj
            (Eq.trans (nat_mul_assoc n n d) (congrArg (fun t => n * t) (Nat.mul_comm n d)))))
        (Eq.symm (nat_mul_assoc r n (d * n))))
  have hE : j' * j = n' * (d * n) :=
    nat_eq_of_sum (K := r * n * (d * n))
      (Nat.mul_comm (d * n) j)
      (Eq.trans (congrArg (fun t => t * j) (Eq.symm hB))
        (Eq.trans (nat_add_mul (r * j) j' j) (congrArg (fun t => t + j' * j) e₃)))
      (Eq.trans (congrArg (fun t => t * (d * n)) (Eq.symm hA)) (nat_add_mul (r * n) n' (d * n)))
  -- Together: `n (j' j') = n (n' n' d)`; cancel `n`.
  have hfin : n * (j' * j') = n * (n' * n' * d) :=
    Eq.trans (Nat.mul_comm n (j' * j'))
      (Eq.trans (nat_mul_assoc j' j' n)
        (Eq.trans (congrArg (fun t => j' * t) hD)
          (Eq.trans (nat_mul_left_comm j' n' j)
            (Eq.trans (congrArg (fun t => n' * t) hE)
              (Eq.trans (Eq.symm (nat_mul_assoc n' n' (d * n)))
                (Eq.trans (Eq.symm (nat_mul_assoc (n' * n') d n))
                  (Nat.mul_comm (n' * n' * d) n)))))))
  exact ⟨n', j', hn'pos, hn'lt, Nat.eq_of_mul_eq_mul_left hn hfin⟩

/-! ## The descent -/

/-- Strong induction by hand: for every bound `N`, no positive `n < N`
has a solution `j² = n²d`. -/
theorem no_square_multiple_aux {d : Nat} (hd : NonSquare d) :
    ∀ N n : Nat, n < N → 0 < n → ∀ j : Nat, j * j = n * n * d → False
  | 0, n, h, _, _, _ => absurd h (Nat.not_lt_zero n)
  | N + 1, _n, h, hn, _j, hj =>
    match descent_step hd hn hj with
    | ⟨n', j', hpos, hlt, hj'⟩ =>
      no_square_multiple_aux hd N n'
        (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ h)) hpos j' hj'

/-- **√d is not a ratio.** If `d` is not a perfect square and `n > 0`, no
`j` has `j² = n²d`. -/
theorem no_square_multiple {d n : Nat} (hd : NonSquare d) (hn : 0 < n) :
    ∀ j : Nat, j * j ≠ n * n * d :=
  fun j hj => no_square_multiple_aux hd (n + 1) n (Nat.lt_succ_self n) hn j hj

/-- **The tick is a non-square.** `NonSquare d → 0 < n → NonSquare (4n²d)`. -/
theorem nonSquare_tick {d n : Nat} (hd : NonSquare d) (hn : 0 < n) :
    NonSquare (4 * n * n * d) :=
  fun k hk =>
    no_square_multiple hd (mul_pos' (Nat.zero_lt_succ 1 : 0 < 2) hn) k
      (Eq.trans hk
        (congrArg (fun t => t * d)
          (Eq.trans (nat_mul_assoc 4 n n) (Eq.symm (mul_mul_self 2 n)))))

/-- `nonSquare_tick` needs `NonSquare d`: at `d = 4`, `4·1·1·4 = 4·4`. -/
theorem nonSquare_tick_needs_nonSquare : ¬ NonSquare (4 * 1 * 1 * 4) :=
  fun h => h 4 rfl

/-- `nonSquare_tick` needs `0 < n`: at `n = 0`, `4·0·0·d = 0·0`. -/
theorem nonSquare_tick_needs_pos (d : Nat) : ¬ NonSquare (4 * 0 * 0 * d) :=
  fun h => h 0 (Eq.symm (Nat.zero_mul d))

/-! ## The walker results, from `NonSquare d` alone -/

/-- **The flip-floor identity**, with no hypothesis beyond `NonSquare d`
and a positive tick. -/
theorem flip_floor_of_nonSquare {d n a a' : Nat} (hd : NonSquare d) (hn : 0 < n)
    (hp : FloorPos d n a) (hm : FloorNeg d n a') : a' = a :=
  flip_floor_of_nonSquare_tick (nonSquare_tick hd hn) hp hm

/-- **The flip reverses the side bit**, from `NonSquare d`. -/
theorem side_hasHand_reverse_of_nonSquare {d n a a' : Nat}
    (hd : NonSquare d) (hn : 0 < n) (hp : FloorPos d n a) (hm : FloorNeg d n a') :
    HasHand (side a a') not not Hand.reverse :=
  side_hasHand_reverse (nonSquare_tick hd hn) hp hm

/-- **A single flip reverses the in-step bit**, from `NonSquare d₁`. -/
theorem inStep_flip₁_reverse_of_nonSquare {d₁ n a₁ a₁' a₂ a₂' : Nat}
    (hd₁ : NonSquare d₁) (hn : 0 < n)
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁') :
    HasHand (inStep a₁ a₁' a₂ a₂') not flip₁ Hand.reverse :=
  inStep_flip₁_reverse (nonSquare_tick hd₁ hn) hp₁ hm₁

/-- **The Phantom Middle keeps the in-step bit**, from `NonSquare d₁` and
`NonSquare d₂`. -/
theorem inStep_phantom_keep_of_nonSquare {d₁ d₂ n a₁ a₁' a₂ a₂' : Nat}
    (hd₁ : NonSquare d₁) (hd₂ : NonSquare d₂) (hn : 0 < n)
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁')
    (hp₂ : FloorPos d₂ n a₂) (hm₂ : FloorNeg d₂ n a₂') :
    HasHand (inStep a₁ a₁' a₂ a₂') not (fun o => flip₁ (flip₂ o)) Hand.keep :=
  inStep_phantom_keep (nonSquare_tick hd₁ hn) hp₁ hm₁ (nonSquare_tick hd₂ hn) hp₂ hm₂

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.mul_lt_mul_right_of_pos
#print axioms PrimitiveReflexivity.ProjectionNecessity.mul_self_lt_of_lt
#print axioms PrimitiveReflexivity.ProjectionNecessity.exists_floor_sqrt
#print axioms PrimitiveReflexivity.ProjectionNecessity.descent_step
#print axioms PrimitiveReflexivity.ProjectionNecessity.no_square_multiple
#print axioms PrimitiveReflexivity.ProjectionNecessity.nonSquare_tick
#print axioms PrimitiveReflexivity.ProjectionNecessity.nonSquare_tick_needs_nonSquare
#print axioms PrimitiveReflexivity.ProjectionNecessity.nonSquare_tick_needs_pos
#print axioms PrimitiveReflexivity.ProjectionNecessity.flip_floor_of_nonSquare
#print axioms PrimitiveReflexivity.ProjectionNecessity.side_hasHand_reverse_of_nonSquare
#print axioms PrimitiveReflexivity.ProjectionNecessity.inStep_flip₁_reverse_of_nonSquare
#print axioms PrimitiveReflexivity.ProjectionNecessity.inStep_phantom_keep_of_nonSquare
