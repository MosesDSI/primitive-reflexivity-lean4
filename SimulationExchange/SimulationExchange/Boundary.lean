/-
  Boundary.lean — the 0.5 boundary, stated exactly in integers.

  A walker's phase at tick n is θ = n·s − k (s·s = d, k ∈ ℤ).
  The orientation flip s ↦ −s acts on phases by the reflection θ ↦ −θ mod 1,
  whose fixed points are exactly the phases with 2θ ∈ ℤ, i.e. θ ∈ {0, ½}.

  §12  The ½ wall is never hit.          (parity alone; any integer d)
  §13  The reflection's fixed points are never occupied.   (needs NonSquare d)
  §14  Side of the wall, as exact integer floors, and the flip.
       Each walker's side bit is inverted by its own sign flip, at every tick.
  §15  The in-step bit: the Phantom Middle (flip both) preserves it at every
       tick; a single flip (σ or τ) inverts it at every tick.
       Uses only that each walker is a non-square — NOT the product condition.
  §15b Parity gate preservation: exchanging the walkers fixes the shared
       coordinate D₁ = a₁ + a₂, negates the depth D₂ = a₁ − a₂, keeps the
       tick, and leaves the in-step gate (the parity of D₂) unchanged.
-/
import SimulationExchange.Core
import SimulationExchange.Model

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange

/-! ## §12  The ½ wall is never hit -/

/-- **The wall is never hit.** In any commutative ring of characteristic 0
    with `s·s = d` for an integer `d`, no phase `θ = n·s − k` satisfies
    `2·θ = 1`. No non-squareness is needed: `(2n)²·d` is even and `(2k+1)²`
    is odd. (For square `d` the phases are integers, never ½, either.) -/
theorem wall_never_hit {R : Type} [CommRing R] [IsCharP R 0]
    (d : Int) (s : R) (hs : s * s = Int.cast d) (n k : Int) :
    (Int.cast 2 : R) * (Int.cast n * s - Int.cast k) ≠ 1 := by
  intro h
  have hR : (Int.cast (4 * (n * n * d) - (4 * (k * k + k) + 1)) : R) = 0 := by grind
  have hZ := int_eq_zero_of_cast _ hR
  generalize n * n * d = u at hZ
  generalize k * k + k = v at hZ
  omega

/-- **The wall result needs characteristic 0.** In `Fin 3`, with `d = 1`,
    `s = 1`, tick `n = 1` and offset `k = 2`, the phase satisfies `2·θ = 1`. -/
theorem wall_needs_charZero :
    (1 : Fin 3) * 1 = 1 ∧ (2 : Fin 3) * ((1 : Fin 3) * 1 - 2) = 1 := by decide

/-! ## §13  The reflection's fixed points are never occupied -/

/-- **No tick sits where the orientations agree.** If `d` is a non-square,
    then at every tick `n ≥ 1`, `2·θ` is not an integer: the walker is never
    at `0` or `½` (mod 1), the two fixed points of the reflection. -/
theorem fixed_points_never_occupied {R : Type} [CommRing R] [IsCharP R 0]
    {d : Nat} (hd : NonSquare d) (s : R) (hs : s * s = Int.cast (d : Int))
    (n k j : Int) (hn : 1 ≤ n) :
    (Int.cast 2 : R) * (Int.cast n * s - Int.cast k) ≠ Int.cast j := by
  intro h
  have hR : (Int.cast ((2 * n) * (2 * n) * (d : Int) - (j + 2 * k) * (j + 2 * k)) : R) = 0 := by
    grind
  have hZ := int_eq_zero_of_cast _ hR
  have := descent_int hd (2 * n) (j + 2 * k) (by omega)
  omega

/-- **Fixed-point avoidance needs `NonSquare d`.** With `d = 4`, `s = 2`,
    tick 1 and offset 2, the phase is `0`, a fixed point (`2·θ = 0`). -/
theorem fixed_points_need_nonSquare :
    ∃ s : Inst 4 3, s * s = Int.cast ((4 : Nat) : Int) ∧
      (Int.cast 2 : Inst 4 3) * (Int.cast (1 : Int) * s - Int.cast (2 : Int)) = Int.cast (0 : Int) :=
  ⟨Int.cast (2 : Int), by ext <;> simp, by ext <;> simp⟩

/-! ## §14  Side of the wall as exact integer floors -/

/-- `a = ⌊2n√d⌋` in the positive orientation, characterized in integers:
    `a² ≤ 4n²d < (a+1)²`. The walker is above the wall (`frac(n√d) > ½`)
    exactly when `a` is odd. -/
def FloorPos (d n a : Nat) : Prop :=
  a * a ≤ 4 * n * n * d ∧ 4 * n * n * d < (a + 1) * (a + 1)

/-- `⌊−2n√d⌋ = −a − 1` in the flipped orientation, characterized in integers:
    `a² < 4n²d ≤ (a+1)²`. The flipped walker is above the wall
    (`frac(−n√d) > ½`) exactly when `−a − 1` is odd, i.e. `a` is even. -/
def FloorNeg (d n a : Nat) : Prop :=
  a * a < 4 * n * n * d ∧ 4 * n * n * d ≤ (a + 1) * (a + 1)

/-- Above the wall, positive orientation. -/
def AbovePos (a : Nat) : Prop := a % 2 = 1
/-- Above the wall, flipped orientation (floor `−a − 1`). -/
def AboveNeg (a : Nat) : Prop := a % 2 = 0

/-- `4n²d` is a non-square at every tick `n ≥ 1` when `d` is. -/
theorem nonSquare_tick {d : Nat} (hd : NonSquare d) (n : Nat) (hn : 1 ≤ n) :
    NonSquare (4 * n * n * d) := by
  intro r hr
  have := descent hd (2 * n) r (by grind)
  omega

/-- Both floors exist at every tick (for non-square `d`). -/
theorem floors_exist {d : Nat} (hd : NonSquare d) (n : Nat) (hn : 1 ≤ n) :
    ∃ a, FloorPos d n a ∧ FloorNeg d n a := by
  obtain ⟨a, h1, h2⟩ := exists_floor_sqrt (4 * n * n * d)
  have hX := nonSquare_tick hd n hn
  have h1' : a * a < 4 * n * n * d := Nat.lt_of_le_of_ne h1 (hX a)
  exact ⟨a, ⟨h1, h2⟩, ⟨h1', Nat.le_of_lt h2⟩⟩

/-- **The flip pins the flipped floor to `−a − 1`.** For non-square `d` and
    `n ≥ 1`, whatever integers certify the two floors, they are the same `a`:
    the floors are `a` and `−a − 1`. -/
theorem flip_floor {d : Nat} (hd : NonSquare d) (n : Nat) (hn : 1 ≤ n)
    (a a' : Nat) (hp : FloorPos d n a) (hm : FloorNeg d n a') : a' = a := by
  have hX := nonSquare_tick hd n hn
  obtain ⟨p1, p2⟩ := hp
  obtain ⟨m1, m2⟩ := hm
  have p1' : a * a < 4 * n * n * d := Nat.lt_of_le_of_ne p1 (hX a)
  have m2' : 4 * n * n * d < (a' + 1) * (a' + 1) := Nat.lt_of_le_of_ne m2 (fun h => hX (a' + 1) h.symm)
  have hlt1 : a < a' + 1 := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_trans p1' m2')
  have hlt2 : a' < a + 1 := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_trans m1 p2)
  omega

/-- **Each flip inverts its walker's side, at every tick.** -/
theorem flip_inverts_side {d : Nat} (hd : NonSquare d) (n : Nat) (hn : 1 ≤ n)
    (a a' : Nat) (hp : FloorPos d n a) (hm : FloorNeg d n a') :
    AboveNeg a' ↔ ¬ AbovePos a := by
  have := flip_floor hd n hn a a' hp hm
  subst this
  unfold AboveNeg AbovePos
  omega

/-- **The flip result needs `NonSquare d`.** With `d = 4` at tick 1, the
    floors are certified by `a = 4` and `a' = 3`, and both orientations put
    the walker below the wall: the flip does not invert the side. -/
theorem flip_needs_nonSquare :
    FloorPos 4 1 4 ∧ FloorNeg 4 1 3 ∧ ¬ AbovePos 4 ∧ ¬ AboveNeg 3 := by
  unfold FloorPos FloorNeg AbovePos AboveNeg; decide

/-! ## §15  The in-step bit and the Phantom Middle -/

/-- **Phantom Middle and single flips, at every tick.** For two walkers with
    non-square `d₁`, `d₂`, at any tick `n ≥ 1`, with floors certified in both
    orientations:
    * flipping both (the Phantom Middle `π`) preserves "in step";
    * flipping only walker 1 (`σ`) inverts it.
    (Flipping only walker 2, `τ`, is the same statement with the roles swapped.)
    The product condition `NonSquare (d₁·d₂)` is not used. -/
theorem phantom_middle_preserves_inStep {d₁ d₂ : Nat}
    (h₁ : NonSquare d₁) (h₂ : NonSquare d₂) (n : Nat) (hn : 1 ≤ n)
    (a₁ a₁' a₂ a₂' : Nat)
    (hp₁ : FloorPos d₁ n a₁) (hm₁ : FloorNeg d₁ n a₁')
    (hp₂ : FloorPos d₂ n a₂) (hm₂ : FloorNeg d₂ n a₂') :
    ((AboveNeg a₁' ↔ AboveNeg a₂') ↔ (AbovePos a₁ ↔ AbovePos a₂)) ∧
    ((AboveNeg a₁' ↔ AbovePos a₂) ↔ ¬ (AbovePos a₁ ↔ AbovePos a₂)) := by
  have e₁ := flip_floor h₁ n hn a₁ a₁' hp₁ hm₁
  have e₂ := flip_floor h₂ n hn a₂ a₂' hp₂ hm₂
  subst e₁ e₂
  unfold AboveNeg AbovePos
  omega

/-- **The single-flip inversion needs walker 1 to be a non-square.** With
    `(d₁, d₂) = (4, 2)` at tick 1 (floors certified: `4, 3` and `2, 2`), the
    walkers are in step in the identity orientation AND still in step after
    flipping walker 1. -/
theorem single_flip_needs_nonSquare :
    FloorPos 4 1 4 ∧ FloorNeg 4 1 3 ∧ FloorPos 2 1 2 ∧ FloorNeg 2 1 2 ∧
    (AbovePos 4 ↔ AbovePos 2) ∧ (AboveNeg 3 ↔ AbovePos 2) := by
  unfold FloorPos FloorNeg AbovePos AboveNeg; decide

/-! ## §15b  Parity gate preservation under the chiral swap

At tick `n` the two walkers' floors `a₁, a₂` split exactly into a shared
coordinate `D₁ = a₁ + a₂` and a difference (depth) coordinate
`D₂ = a₁ − a₂` (integer form, no halving: `2a₁ = D₁ + D₂`, `2a₂ = D₁ − D₂`).
The chiral swap exchanges the two walkers at the same tick. It negates `D₂`
and fixes `D₁`, the in-step gate reads only the parity of `D₂`, and the tick
is untouched. Pure parity: no hypothesis on `d₁, d₂` is used. -/

/-- Shared coordinate of the two floors. -/
def D₁ (a₁ a₂ : Nat) : Int := (a₁ : Int) + a₂
/-- Difference (depth) coordinate of the two floors. -/
def D₂ (a₁ a₂ : Nat) : Int := (a₁ : Int) - a₂

/-- The split is exact. -/
theorem split_exact (a₁ a₂ : Nat) :
    D₁ a₁ a₂ + D₂ a₁ a₂ = 2 * a₁ ∧ D₁ a₁ a₂ - D₂ a₁ a₂ = 2 * a₂ := by
  unfold D₁ D₂; omega

/-- **The in-step gate reads the depth's parity.** Two walkers are in step
    exactly when `D₂` is even. -/
theorem inStep_iff_D₂_even (a₁ a₂ : Nat) :
    (AbovePos a₁ ↔ AbovePos a₂) ↔ D₂ a₁ a₂ % 2 = 0 := by
  unfold AbovePos D₂; omega

/-- **Parity gate preservation.** Swapping the walkers at tick `n` keeps both
    floors certified at the same tick `n` (the carrier is not displaced),
    fixes `D₁`, negates `D₂`, and leaves the in-step gate unchanged. -/
theorem chiral_swap_preserves_gate {d₁ d₂ n a₁ a₂ : Nat}
    (hp₁ : FloorPos d₁ n a₁) (hp₂ : FloorPos d₂ n a₂) :
    (FloorPos d₂ n a₂ ∧ FloorPos d₁ n a₁) ∧
    D₁ a₂ a₁ = D₁ a₁ a₂ ∧ D₂ a₂ a₁ = -D₂ a₁ a₂ ∧
    ((AbovePos a₂ ↔ AbovePos a₁) ↔ (AbovePos a₁ ↔ AbovePos a₂)) := by
  refine ⟨⟨hp₂, hp₁⟩, by unfold D₁; omega, by unfold D₂; omega, Iff.intro Iff.symm Iff.symm⟩

/-- The gate does not care which of `D₁`, `D₂` it reads: they have the same
    parity, so the shared coordinate carries the same in-step bit. -/
theorem D₁_D₂_same_parity (a₁ a₂ : Nat) : D₁ a₁ a₂ % 2 = D₂ a₁ a₂ % 2 := by
  unfold D₁ D₂; omega

/-- Identical floors have no depth. -/
theorem D₂_eq_zero_iff (a₁ a₂ : Nat) : D₂ a₁ a₂ = 0 ↔ a₁ = a₂ := by
  unfold D₂; omega

/-! ## §16  Instances: the trap `(30, 33)` -/

/-- The trap's walkers satisfy every hypothesis of §15. -/
theorem trap_phantom_middle_preserves_inStep (n : Nat) (hn : 1 ≤ n)
    (a₁ a₁' a₂ a₂' : Nat)
    (hp₁ : FloorPos 30 n a₁) (hm₁ : FloorNeg 30 n a₁')
    (hp₂ : FloorPos 33 n a₂) (hm₂ : FloorNeg 33 n a₂') :
    ((AboveNeg a₁' ↔ AboveNeg a₂') ↔ (AbovePos a₁ ↔ AbovePos a₂)) ∧
    ((AboveNeg a₁' ↔ AbovePos a₂) ↔ ¬ (AbovePos a₁ ↔ AbovePos a₂)) :=
  phantom_middle_preserves_inStep nonSquare_30 nonSquare_33 n hn a₁ a₁' a₂ a₂' hp₁ hm₁ hp₂ hm₂

/-- Non-vacuity: at tick 1 the trap's floors are certified by explicit
    integers (`⌊2√30⌋ = 10`, `⌊2√33⌋ = 11`), so the hypotheses are met. -/
theorem trap_tick1_floors :
    FloorPos 30 1 10 ∧ FloorNeg 30 1 10 ∧ FloorPos 33 1 11 ∧ FloorNeg 33 1 11 := by
  unfold FloorPos FloorNeg; decide

/-- At tick 1 the trap's walkers are out of step (walker 1 below, walker 2
    above) — and by §15 the Phantom Middle keeps them out of step. -/
theorem trap_tick1_out_of_step : ¬ (AbovePos 10 ↔ AbovePos 11) := by
  unfold AbovePos; decide

/-- The swap at the trap's tick 1: `D₁ = 21` stays, `D₂ = −1` becomes `+1`,
    and the gate (odd depth: out of step) is the same on both sides. -/
theorem trap_tick1_chiral_swap :
    D₁ 10 11 = 21 ∧ D₁ 11 10 = 21 ∧ D₂ 10 11 = -1 ∧ D₂ 11 10 = 1 ∧
    ¬ (AbovePos 10 ↔ AbovePos 11) ∧ ¬ (AbovePos 11 ↔ AbovePos 10) := by
  unfold D₁ D₂ AbovePos; decide

end SimulationExchange
