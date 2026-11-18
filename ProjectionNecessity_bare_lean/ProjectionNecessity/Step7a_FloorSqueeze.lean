/-
  Projection Necessity, Step 7a: the floor squeeze.

  Bare Lean 4. Imports only `ZeroInt` (zero-axiom `Nat`/`Int` arithmetic).
  Nothing is imported from `SimulationExchange`, whose versions of these
  results depend on `propext`, `Classical.choice` and `Quot.sound`.

  Hygiene, as in Steps 1–6: no `simp`, `omega`, `decide` or `by_cases`,
  and none of ZeroInt's `nat_ring` / `int_ring` macros. Only ZeroInt's
  proved lemmas are used, by name. Target: zero axioms for every
  declaration.

  Results.

  * `mul_self_le_mul_self`: `a ≤ b → a * a ≤ b * b`, from
    `ZeroInt.nat_add_mul` and left distributivity.
  * `lt_of_mul_self_lt_mul_self`: `a * a < b * b → a < b`.
  * `squeeze`: `a² < (a'+1)²` and `a'² < (a+1)²` force `a' = a`.
  * `floor_squeeze`: the same, through a shared value `X` between them.
  * `flip_floor_of_nonSquare_tick`: the flip-floor identity. If `4n²d` is
    not a perfect square, the integers certifying the positive floor
    (`FloorPos`) and the flipped floor (`FloorNeg`) are the same `a`.

  The hypothesis `NonSquare (4 * n * n * d)` is discharged from
  `NonSquare d` in Step 7 sub-step (1), the descent.

  `NonSquare`, `FloorPos` and `FloorNeg` restate the definitions in
  `SimulationExchange/SimulationExchange/{Core,Boundary}.lean` with the
  same shape.
-/

import ProjectionNecessity.ZeroInt

set_option genInjectivity false

namespace PrimitiveReflexivity.ProjectionNecessity

/-! ## Monotonicity of squaring on `Nat` -/

/-- Squaring is monotone: `a ≤ b → a * a ≤ b * b`. Write `b = a + k`;
then `b * b = a * a + (a * k + k * (a + k))`. -/
theorem mul_self_le_mul_self {a b : Nat} (h : a ≤ b) : a * a ≤ b * b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  have e : (a + k) * (a + k) = a * a + (a * k + k * (a + k)) :=
    Eq.trans (DSISVerification.ZeroInt.nat_add_mul a k (a + k))
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

/-! ## The squeeze -/

/-- **The squeeze.** `a² < (a'+1)²` and `a'² < (a+1)²` force `a' = a`:
the first gives `a ≤ a'`, the second `a' ≤ a`. -/
theorem squeeze {a a' : Nat}
    (h₁ : a * a < (a' + 1) * (a' + 1)) (h₂ : a' * a' < (a + 1) * (a + 1)) :
    a' = a :=
  Nat.le_antisymm
    (Nat.le_of_lt_succ (lt_of_mul_self_lt_mul_self h₂))
    (Nat.le_of_lt_succ (lt_of_mul_self_lt_mul_self h₁))

/-- **The floor squeeze.** If `a² < X < (a'+1)²` and `a'² < X < (a+1)²`,
then `a' = a`. -/
theorem floor_squeeze {X a a' : Nat}
    (h₁ : a * a < X) (h₂ : X < (a' + 1) * (a' + 1))
    (h₃ : a' * a' < X) (h₄ : X < (a + 1) * (a + 1)) : a' = a :=
  squeeze (Nat.lt_trans h₁ h₂) (Nat.lt_trans h₃ h₄)

/-! ## The flip-floor identity -/

/-- `d` is not a perfect square. (Same shape as `SimulationExchange.NonSquare`.) -/
def NonSquare (d : Nat) : Prop :=
  ∀ r : Nat, r * r ≠ d

/-- `a = ⌊2n√d⌋`, in integers: `a² ≤ 4n²d < (a+1)²`.
(Same shape as `SimulationExchange.FloorPos`.) -/
def FloorPos (d n a : Nat) : Prop :=
  a * a ≤ 4 * n * n * d ∧ 4 * n * n * d < (a + 1) * (a + 1)

/-- The flipped floor `⌊−2n√d⌋ = −a − 1`, in integers: `a² < 4n²d ≤ (a+1)²`.
(Same shape as `SimulationExchange.FloorNeg`.) -/
def FloorNeg (d n a : Nat) : Prop :=
  a * a < 4 * n * n * d ∧ 4 * n * n * d ≤ (a + 1) * (a + 1)

/-- **The flip-floor identity.** If `4n²d` is not a perfect square, the
integers certifying the positive and the flipped floor coincide. The
non-squareness turns both non-strict bounds strict, and the squeeze does
the rest. -/
theorem flip_floor_of_nonSquare_tick {d n a a' : Nat}
    (hX : NonSquare (4 * n * n * d))
    (hp : FloorPos d n a) (hm : FloorNeg d n a') : a' = a :=
  floor_squeeze
    (Nat.lt_of_le_of_ne hp.1 (hX a))
    (Nat.lt_of_le_of_ne hm.2 (fun h => hX (a' + 1) (Eq.symm h)))
    hm.1
    hp.2

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.mul_self_le_mul_self
#print axioms PrimitiveReflexivity.ProjectionNecessity.lt_of_mul_self_lt_mul_self
#print axioms PrimitiveReflexivity.ProjectionNecessity.squeeze
#print axioms PrimitiveReflexivity.ProjectionNecessity.floor_squeeze
#print axioms PrimitiveReflexivity.ProjectionNecessity.flip_floor_of_nonSquare_tick
