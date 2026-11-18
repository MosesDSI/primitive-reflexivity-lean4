/-
  Projection Necessity, Step 7b: parity bookkeeping.

  Bare Lean 4. Imports Step 6 (handedness, with Steps 5 and 3) and
  Step 7a (the floor squeeze, with ZeroInt). Nothing from
  `SimulationExchange`, `Real` or `Rat`.

  Hygiene, as in Steps 1–7a: no `simp`, `omega`, `decide`, `by_cases` or
  `grind`, and none of ZeroInt's macros. No `Nat.mod` lemmas: parity is
  defined by recursion and tied to the decomposition `n = 2q + r`
  directly. Target: zero axioms for every declaration.

  Results.

  * `parity`, with `parity_spec` (every `n` is `2q + r`, `r` its parity
    bit) and `parity_two_mul_add` / `parity_unique` (any decomposition
    determines the bit). So `parity a = true` says exactly "`a` is odd",
    the content of `SimulationExchange.AbovePos a := a % 2 = 1`.
  * `side a a' o`: a walker's side bit in orientation `o`. Positive
    (`false`): above the wall iff the floor `a` is odd. Flipped (`true`):
    the floor is `−a' − 1`, above iff `a'` is even.
  * `side_hasHand_reverse`: under the flip-floor identity (Step 7a), the
    flip acts on the side bit as `not`: hand `reverse`.
    `side_two_flips_keep`: two flips have hand `keep` (Step 6's sign law).
  * `inStep_flip₁_reverse`, `inStep_flip₂_reverse`: a single flip
    reverses the in-step bit. `inStep_phantom_keep`: the Phantom Middle
    (flip both) keeps it.
  * `side_offTheWall`, `inStep_offTheWall`, and with them
    `flip_moves_every_side_cell`, `phantom_middle_fixes_every_inStep_cell`,
    `flip₁_moves_every_inStep_cell`: the conclusions of Step 6 hold for
    the walkers.
  * `side_flip_needs_flipFloor`: at `d = 4`, tick 1 (floors `4` and `3`,
    so `a' ≠ a`), the flip does not reverse the side bit. The flip-floor
    identity is needed.
-/

import ProjectionNecessity.Step6_Handedness
import ProjectionNecessity.Step7a_FloorSqueeze

set_option genInjectivity false

namespace PrimitiveReflexivity.ProjectionNecessity

/-! ## Booleans -/

/-- Negating twice is the identity. -/
theorem not_not_bool : ∀ b : Bool, (!(!b)) = b
  | true => rfl
  | false => rfl

/-- `not` is an involution, in the sense of Step 6. -/
theorem not_involution : Involution not :=
  not_not_bool

/-- No boolean is its own negation. -/
theorem not_ne_self : ∀ b : Bool, (!b) ≠ b
  | true => fun h => Bool.false_ne_true (h : false = true)
  | false => fun h => Bool.false_ne_true (Eq.symm (h : true = false))

/-! ## Parity, by recursion -/

/-- Parity of a natural number: `true` for odd. -/
def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

/-- The remainder named by a parity bit. -/
def bitVal : Bool → Nat
  | false => 0
  | true => 1

/-- **Every `n` is `2q + r`, with `r` its parity bit.** -/
theorem parity_spec : ∀ n : Nat, ∃ q : Nat, n = 2 * q + bitVal (parity n)
  | 0 => ⟨0, rfl⟩
  | n + 1 => by
    obtain ⟨q, hq⟩ := parity_spec n
    cases hp : parity n with
    | false =>
      rw [hp] at hq
      refine ⟨q, ?_⟩
      show n + 1 = 2 * q + bitVal (!(parity n))
      rw [hp]
      exact congrArg (fun x => x + 1) hq
    | true =>
      rw [hp] at hq
      refine ⟨q + 1, ?_⟩
      show n + 1 = 2 * (q + 1) + bitVal (!(parity n))
      rw [hp]
      exact congrArg (fun x => x + 1) hq

/-- **A decomposition determines the bit.** `parity (2q + r) = b` when `r`
is the remainder named by `b`. -/
theorem parity_two_mul_add : ∀ (q : Nat) (b : Bool), parity (2 * q + bitVal b) = b
  | 0, false => rfl
  | 0, true => rfl
  | q + 1, b =>
    have e : 2 * (q + 1) + bitVal b = 2 * q + bitVal b + 2 :=
      Eq.trans (Nat.add_assoc (2 * q) 2 (bitVal b))
        (Eq.trans (congrArg (fun t => 2 * q + t) (Nat.add_comm 2 (bitVal b)))
          (Eq.symm (Nat.add_assoc (2 * q) (bitVal b) 2)))
    Eq.trans (congrArg parity e)
      (Eq.trans (not_not_bool (parity (2 * q + bitVal b))) (parity_two_mul_add q b))

/-- **The parity bit of a decomposition is unique.** -/
theorem parity_unique {q q' : Nat} {b b' : Bool}
    (h : 2 * q + bitVal b = 2 * q' + bitVal b') : b = b' :=
  Eq.trans (Eq.symm (parity_two_mul_add q b))
    (Eq.trans (congrArg parity h) (parity_two_mul_add q' b'))

/-! ## The side bit of one walker -/

/-- A walker's side bit in orientation `o`, from its two floor
certificates: `a` (positive, `FloorPos`) and `a'` (flipped, `FloorNeg`).
Positive orientation: above the wall iff `a` is odd. Flipped: the floor
is `−a' − 1`, above iff `a'` is even. -/
def side (a a' : Nat) : Bool → Bool
  | false => parity a
  | true => !(parity a')

/-- If the two certificates agree, the flip negates the side bit. -/
theorem side_flip {a a' : Nat} (h : a' = a) : ∀ o : Bool, side a a' (!o) = !(side a a' o)
  | false => congrArg (fun x => !(parity x)) h
  | true => Eq.trans (congrArg parity (Eq.symm h)) (Eq.symm (not_not_bool (parity a')))

/-- **The flip reverses the side bit.** Under the flip-floor identity
(`NonSquare (4n²d)`, both floors certified), flipping the orientation
has hand `reverse` on the side bit. -/
theorem side_hasHand_reverse {d n a a' : Nat}
    (hX : NonSquare (4 * n * n * d)) (hp : FloorPos d n a) (hm : FloorNeg d n a') :
    HasHand (side a a') not not Hand.reverse :=
  side_flip (flip_floor_of_nonSquare_tick hX hp hm)

/-- **Two flips keep the side bit.** By Step 6's sign law, reverse after
reverse is keep. -/
theorem side_two_flips_keep {d n a a' : Nat}
    (hX : NonSquare (4 * n * n * d)) (hp : FloorPos d n a) (hm : FloorNeg d n a') :
    HasHand (side a a') not (fun o => !(!o)) Hand.keep :=
  hasHand_comp not_involution
    (side_hasHand_reverse hX hp hm) (side_hasHand_reverse hX hp hm)

/-! ## The in-step bit of two walkers -/

/-- Agreement of two bits: `true` when they are equal. -/
def agree : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | true, false => false
  | false, true => false

theorem agree_not_left : ∀ x y : Bool, agree (!x) y = !(agree x y)
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

theorem agree_not_right : ∀ x y : Bool, agree x (!y) = !(agree x y)
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

/-- The in-step bit: are the two walkers on the same side of their
walls, given the orientations `o = (o₁, o₂)`? -/
def inStep (a₁ a₁' a₂ a₂' : Nat) (o : Bool × Bool) : Bool :=
  agree (side a₁ a₁' o.1) (side a₂ a₂' o.2)

/-- Flip walker 1. -/
def flip₁ (o : Bool × Bool) : Bool × Bool := (!o.1, o.2)

/-- Flip walker 2. -/
def flip₂ (o : Bool × Bool) : Bool × Bool := (o.1, !o.2)

/-- **Flipping walker 1 reverses the in-step bit.** -/
theorem inStep_flip₁_reverse {d₁ n a₁ a₁' a₂ a₂' : Nat}
    (hX₁ : NonSquare (4 * n * n * d₁))
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁') :
    HasHand (inStep a₁ a₁' a₂ a₂') not flip₁ Hand.reverse :=
  fun o =>
    Eq.trans
      (congrArg (fun x => agree x (side a₂ a₂' o.2))
        (side_flip (flip_floor_of_nonSquare_tick hX₁ hp₁ hm₁) o.1))
      (agree_not_left (side a₁ a₁' o.1) (side a₂ a₂' o.2))

/-- **Flipping walker 2 reverses the in-step bit.** -/
theorem inStep_flip₂_reverse {d₂ n a₁ a₁' a₂ a₂' : Nat}
    (hX₂ : NonSquare (4 * n * n * d₂))
    (hp₂ : FloorPos d₂ n a₂) (hm₂ : FloorNeg d₂ n a₂') :
    HasHand (inStep a₁ a₁' a₂ a₂') not flip₂ Hand.reverse :=
  fun o =>
    Eq.trans
      (congrArg (fun x => agree (side a₁ a₁' o.1) x)
        (side_flip (flip_floor_of_nonSquare_tick hX₂ hp₂ hm₂) o.2))
      (agree_not_right (side a₁ a₁' o.1) (side a₂ a₂' o.2))

/-- **The Phantom Middle keeps the in-step bit.** Flipping both walkers
is reverse after reverse, which is keep (Step 6). -/
theorem inStep_phantom_keep {d₁ d₂ n a₁ a₁' a₂ a₂' : Nat}
    (hX₁ : NonSquare (4 * n * n * d₁))
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁')
    (hX₂ : NonSquare (4 * n * n * d₂))
    (hp₂ : FloorPos d₂ n a₂) (hm₂ : FloorNeg d₂ n a₂') :
    HasHand (inStep a₁ a₁' a₂ a₂') not (fun o => flip₁ (flip₂ o)) Hand.keep :=
  hasHand_comp not_involution
    (inStep_flip₁_reverse hX₁ hp₁ hm₁) (inStep_flip₂_reverse hX₂ hp₂ hm₂)

/-! ## Off the wall, and the Step 6 conclusions for the walkers -/

/-- **No side reading is on the wall.** `not` changes every reading. -/
theorem side_offTheWall (a a' : Nat) : OffTheWall (side a a') not :=
  fun o => not_ne_self (side a a' o)

/-- **No in-step reading is on the wall.** -/
theorem inStep_offTheWall (a₁ a₁' a₂ a₂' : Nat) :
    OffTheWall (inStep a₁ a₁' a₂ a₂') not :=
  fun o => not_ne_self (inStep a₁ a₁' a₂ a₂' o)

/-- **The flip moves every side cell** (Step 6, `reverse_moves_every_cell`). -/
theorem flip_moves_every_side_cell {d n a a' : Nat}
    (hX : NonSquare (4 * n * n * d)) (hp : FloorPos d n a) (hm : FloorNeg d n a')
    (o : Bool) : project (side a a') (!o) ≠ project (side a a') o :=
  reverse_moves_every_cell (side_offTheWall a a') (side_hasHand_reverse hX hp hm) o

/-- **A single flip moves every in-step cell.** -/
theorem flip₁_moves_every_inStep_cell {d₁ n a₁ a₁' a₂ a₂' : Nat}
    (hX₁ : NonSquare (4 * n * n * d₁))
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁') (o : Bool × Bool) :
    project (inStep a₁ a₁' a₂ a₂') (flip₁ o) ≠ project (inStep a₁ a₁' a₂ a₂') o :=
  reverse_moves_every_cell (inStep_offTheWall a₁ a₁' a₂ a₂')
    (inStep_flip₁_reverse hX₁ hp₁ hm₁) o

/-- **The Phantom Middle fixes every in-step cell** (Step 5,
`project_invariant`). -/
theorem phantom_middle_fixes_every_inStep_cell {d₁ d₂ n a₁ a₁' a₂ a₂' : Nat}
    (hX₁ : NonSquare (4 * n * n * d₁))
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁')
    (hX₂ : NonSquare (4 * n * n * d₂))
    (hp₂ : FloorPos d₂ n a₂) (hm₂ : FloorNeg d₂ n a₂') (o : Bool × Bool) :
    project (inStep a₁ a₁' a₂ a₂') (flip₁ (flip₂ o)) = project (inStep a₁ a₁' a₂ a₂') o :=
  project_invariant (inStep_phantom_keep hX₁ hp₁ hm₁ hX₂ hp₂ hm₂) o

/-! ## Necessity of the flip-floor identity -/

/-- **The flip needs the flip-floor identity.** At `d = 4`, tick 1, the
floors are certified by `a = 4` and `a' = 3` (`16 ≤ 16 < 25` and
`9 < 16 ≤ 16`), so `a' ≠ a`, and the flip does not reverse the side bit:
both orientations read "below". -/
theorem side_flip_needs_flipFloor :
    FloorPos 4 1 4 ∧ FloorNeg 4 1 3 ∧ ¬ HasHand (side 4 3) not not Hand.reverse :=
  ⟨⟨(Nat.le_of_ble_eq_true rfl : 4 * 4 ≤ 4 * 1 * 1 * 4),
    (Nat.le_of_ble_eq_true rfl : 4 * 1 * 1 * 4 + 1 ≤ (4 + 1) * (4 + 1))⟩,
   ⟨(Nat.le_of_ble_eq_true rfl : 3 * 3 + 1 ≤ 4 * 1 * 1 * 4),
    (Nat.le_of_ble_eq_true rfl : 4 * 1 * 1 * 4 ≤ (3 + 1) * (3 + 1))⟩,
   fun h => Bool.false_ne_true (h false : false = true)⟩

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.not_ne_self
#print axioms PrimitiveReflexivity.ProjectionNecessity.parity_spec
#print axioms PrimitiveReflexivity.ProjectionNecessity.parity_two_mul_add
#print axioms PrimitiveReflexivity.ProjectionNecessity.parity_unique
#print axioms PrimitiveReflexivity.ProjectionNecessity.side_hasHand_reverse
#print axioms PrimitiveReflexivity.ProjectionNecessity.side_two_flips_keep
#print axioms PrimitiveReflexivity.ProjectionNecessity.inStep_flip₁_reverse
#print axioms PrimitiveReflexivity.ProjectionNecessity.inStep_flip₂_reverse
#print axioms PrimitiveReflexivity.ProjectionNecessity.inStep_phantom_keep
#print axioms PrimitiveReflexivity.ProjectionNecessity.side_offTheWall
#print axioms PrimitiveReflexivity.ProjectionNecessity.inStep_offTheWall
#print axioms PrimitiveReflexivity.ProjectionNecessity.flip_moves_every_side_cell
#print axioms PrimitiveReflexivity.ProjectionNecessity.flip₁_moves_every_inStep_cell
#print axioms PrimitiveReflexivity.ProjectionNecessity.phantom_middle_fixes_every_inStep_cell
#print axioms PrimitiveReflexivity.ProjectionNecessity.side_flip_needs_flipFloor
