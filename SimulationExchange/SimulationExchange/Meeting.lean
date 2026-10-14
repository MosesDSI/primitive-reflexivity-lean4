/-
  Meeting.lean — the meeting walker (the fall walker) is faithful.

  Two walkers at phases θ₁ = n·s − k₁ and θ₂ = n·t − k₂ (s·s = d₁, t·t = d₂).
  Their separation θ₁ − θ₂ = n·(s − t) − (k₁ − k₂) is itself a walker, with
  step s − t: the signed difference, the D2 ("fall") component of the pair.
  How often the two walkers come near each other is a statistic of this one
  derived walker.

  §17  The meeting walker never revisits a phase: if (n − m)·(s − t) is an
       integer then n = m. Only NonSquare (d₁·d₂) is needed — neither d₁ nor
       d₂ has to be a non-square on its own.
  §18  Necessity of each hypothesis, and non-vacuity.
-/
import SimulationExchange.Core
import SimulationExchange.Model

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange

/-! ## §17  The meeting walker is faithful -/

/-- **The meeting walker is faithful.** In a commutative ring of
    characteristic 0 with `s·s = d₁`, `t·t = d₂` and `d₁·d₂` a non-square:
    if ticks `n` and `m` put the separation walker (step `s − t`) at the same
    phase — i.e. `(n − m)·(s − t)` is an integer `j` — then `n = m`.

    Proof: square once to isolate `s·t` as a rational, square again so that
    `(2k²)²·(d₁d₂)` is a perfect square, and apply `descent` to `d₁·d₂`. -/
theorem meeting_faithful {R : Type} [CommRing R] [IsCharP R 0]
    {d₁ d₂ : Nat} (h₁₂ : NonSquare (d₁ * d₂))
    (s t : R) (hs : s * s = Int.cast (d₁ : Int)) (ht : t * t = Int.cast (d₂ : Int))
    (n m j : Int) (h : Int.cast (n - m) * (s - t) = (Int.cast j : R)) : n = m := by
  generalize hk : n - m = k at h
  -- first squaring: 2k²·(s·t) = k²(d₁ + d₂) − j²
  have hsq : (Int.cast k * (s - t)) * (Int.cast k * (s - t)) = (Int.cast j : R) * Int.cast j := by
    rw [h]
  have hst : (Int.cast (2 * k * k) : R) * (s * t)
      = Int.cast (k * k * ((d₁ : Int) + d₂) - j * j) := by
    grind
  -- second squaring: (2k²)²·(d₁d₂) = u²
  have h4 : (Int.cast ((2 * k * k) * (2 * k * k) * (((d₁ * d₂ : Nat)) : Int)
      - (k * k * ((d₁ : Int) + d₂) - j * j) * (k * k * ((d₁ : Int) + d₂) - j * j)) : R) = 0 := by
    have hprod : (s * t) * (s * t) = (Int.cast ((d₁ : Int) * d₂) : R) := by grind
    have := congrArg (fun x => x * x) hst
    push_cast
    grind
  have hZ := int_eq_zero_of_cast _ h4
  have h2k := descent_int h₁₂ (2 * k * k) (k * k * ((d₁ : Int) + d₂) - j * j) (by omega)
  have hkk : k * k = 0 := by
    have : 2 * (k * k) = 0 := by rw [← Int.mul_assoc]; exact h2k
    omega
  have := int_mul_self_eq_zero hkk
  omega

/-! ## §18  Necessity and non-vacuity -/

open Inst

/-- **The product hypothesis is needed.** With `(d₁, d₂) = (2, 2)` (product 4,
    a square) take `s = t = x₁`: the meeting walker never moves, so ticks
    `1` and `0` put it at the same phase although `1 ≠ 0`. -/
theorem meeting_needs_product :
    ∃ s t : Inst 2 2, s * s = Int.cast ((2 : Nat) : Int) ∧ t * t = Int.cast ((2 : Nat) : Int) ∧
      Int.cast ((1 : Int) - 0) * (s - t) = Int.cast (0 : Int) ∧ (1 : Int) ≠ 0 :=
  ⟨x₁, x₁, x₁_sq, x₁_sq, by ext <;> simp [x₁], by decide⟩

/-- **`hs` is needed.** In `Inst 2 3`, take `t = x₂` (so `t·t = 3`) and
    `s = x₂ + 1`, which is not a square root of 2. Then `s − t = 1` and every
    tick difference lands on an integer. -/
theorem meeting_needs_hs :
    ∃ s t : Inst 2 3, t * t = Int.cast ((3 : Nat) : Int) ∧ s * s ≠ Int.cast ((2 : Nat) : Int) ∧
      Int.cast ((1 : Int) - 0) * (s - t) = Int.cast (1 : Int) ∧ (1 : Int) ≠ 0 := by
  refine ⟨x₂ + 1, x₂, x₂_sq, ?_, ?_, by decide⟩
  · intro h; have := congrArg Inst.a h; simp [x₂] at this
  · ext <;> simp [x₂]

/-- **`ht` is needed.** The mirror image: `s = x₁` (so `s·s = 2`) and
    `t = x₁ + 1`, not a square root of 3. Then `s − t = −1`. -/
theorem meeting_needs_ht :
    ∃ s t : Inst 2 3, s * s = Int.cast ((2 : Nat) : Int) ∧ t * t ≠ Int.cast ((3 : Nat) : Int) ∧
      Int.cast ((1 : Int) - 0) * (s - t) = Int.cast (-1 : Int) ∧ (1 : Int) ≠ 0 := by
  refine ⟨x₁, x₁ + 1, x₁_sq, ?_, ?_, by decide⟩
  · intro h; have := congrArg Inst.b h; simp [x₁] at this
  · ext <;> simp [x₁]

/-- Non-vacuity: the trap `(30, 33)`, inside its own instructure model. -/
theorem trap_meeting_faithful (n m j : Int)
    (h : Int.cast (n - m) * ((x₁ : Inst 30 33) - x₂) = Int.cast j) : n = m :=
  meeting_faithful (d₁ := 30) (d₂ := 33) nonSquare_990 x₁ x₂ x₁_sq x₂_sq n m j h

/-- The premise is satisfiable in the model (at `n = m`, as the theorem
    predicts), so the theorem is not vacuous. -/
theorem trap_meeting_premise_satisfiable :
    Int.cast ((5 : Int) - 5) * ((x₁ : Inst 30 33) - x₂) = Int.cast (0 : Int) := by
  ext <;> simp [x₁, x₂]

/-- **Neither walker needs to be irrational on its own.** With `(d₁, d₂) = (4, 2)`
    walker 1 is the rational step `s = 2`, yet `4·2 = 8` is a non-square, so the
    meeting walker is still faithful. -/
theorem meeting_faithful_rational_first (n m j : Int)
    (h : Int.cast (n - m) * ((Int.cast (2 : Int) : Inst 4 2) - x₂) = Int.cast j) : n = m :=
  meeting_faithful (d₁ := 4) (d₂ := 2) (nonSquare_of_between 8 2 (by decide) (by decide))
    (Int.cast (2 : Int)) x₂ (by ext <;> simp) x₂_sq n m j h

end SimulationExchange
