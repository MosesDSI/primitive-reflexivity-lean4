/-
  Instances.lean — the exchange theorems applied inside the kernel-checked
  instructure model, plus ring-level counterexamples showing every
  hypothesis is necessary.
-/
import SimulationExchange.Core
import SimulationExchange.Model

open Lean.Grind

namespace SimulationExchange
open Inst

/-! ## §7  Non-vacuity: the trap `(30, 33)` inside its own instructure -/

/-- Theorem A, applied to the trap's walker 1 (`x₁ · x₁ = 30`). -/
theorem trap_faithful (n m j : Int)
    (h : Int.cast (n - m) * (x₁ : Inst 30 33) = Int.cast j) : n = m :=
  faithful (d := 30) nonSquare_30 x₁ x₁_sq n m j h

/-- Corollary A′, applied to the trap: walker 1's coincidences force walker 2's. -/
theorem trap_walker1_determines_walker2 (n m j : Int)
    (h : Int.cast (n - m) * (x₁ : Inst 30 33) = Int.cast j) :
    ∃ j₂ : Int, Int.cast (n - m) * (x₂ : Inst 30 33) = Int.cast j₂ :=
  walker1_determines_walker2 (d₁ := 30) nonSquare_30 x₁ x₂ x₁_sq n m j h

/-- Theorem B, applied to the trap: no rational affine rule links the walkers. -/
theorem trap_no_direct_rule (n v u w k₁ k₂ : Int) (hn : 1 ≤ n) (hv : 1 ≤ v)
    (θ₁ θ₂ : Inst 30 33) (e₁ : θ₁ = Int.cast n * x₁ - Int.cast k₁)
    (e₂ : θ₂ = Int.cast n * x₂ - Int.cast k₂)
    (rule : Int.cast v * θ₂ = Int.cast u * θ₁ + Int.cast w) : False :=
  no_direct_rule (d₁ := 30) (d₂ := 33) nonSquare_33 nonSquare_990 x₁ x₂ x₁_sq x₂_sq
    n v u w k₁ k₂ hn hv θ₁ θ₂ e₁ e₂ rule

/-- The hypotheses of Theorem A are jointly satisfiable in the model
    (at `n = m`, as faithfulness predicts), so Theorem A is not vacuous. -/
theorem trap_faithful_premise_satisfiable :
    Int.cast ((7 : Int) - 7) * (x₁ : Inst 30 33) = Int.cast (0 : Int) := by
  ext <;> simp [x₁]

/-- The phase equations of Theorem B are satisfiable in the model, so the
    theorem's content is exactly the impossibility of the rule. -/
theorem trap_phases_exist :
    ∃ θ₁ θ₂ : Inst 30 33,
      θ₁ = Int.cast (1 : Int) * x₁ - Int.cast (5 : Int) ∧
      θ₂ = Int.cast (1 : Int) * x₂ - Int.cast (5 : Int) :=
  ⟨_, _, rfl, rfl⟩

/-! ## §8  Necessity at the ring level: dropping a hypothesis breaks the conclusion -/

theorem nonSquare_8 : NonSquare 8 := nonSquare_of_between 8 2 (by decide) (by decide)
theorem nonSquare_2x4 : NonSquare (2 * 4) := nonSquare_8
theorem nonSquare_4x2 : NonSquare (4 * 2) := nonSquare_8

/-- **Theorem A needs `NonSquare d`.** With `d = 4` and `s = 2` (so `s·s = 4`),
    ticks `1` and `0` render to the same phase, yet `1 ≠ 0`. -/
theorem faithful_needs_nonSquare :
    ∃ s : Inst 4 2, s * s = Int.cast ((4 : Nat) : Int) ∧
      Int.cast ((1 : Int) - 0) * s = Int.cast (2 : Int) ∧ (1 : Int) ≠ 0 :=
  ⟨Int.cast (2 : Int), by ext <;> simp, by ext <;> simp, by decide⟩

/-- **Theorem B needs `NonSquare (d₁·d₂)`.** With `(d₁, d₂) = (2, 8)`, both
    non-squares but with square product 16, take `t = 2·s`. Then at tick 1
    the rule `θ₂ = 2·θ₁` holds exactly. -/
theorem no_direct_rule_needs_product :
    ∃ s t θ₁ θ₂ : Inst 2 8,
      s * s = Int.cast ((2 : Nat) : Int) ∧ t * t = Int.cast ((8 : Nat) : Int) ∧
      θ₁ = Int.cast (1 : Int) * s - Int.cast (0 : Int) ∧
      θ₂ = Int.cast (1 : Int) * t - Int.cast (0 : Int) ∧
      Int.cast (1 : Int) * θ₂ = Int.cast (2 : Int) * θ₁ + Int.cast (0 : Int) := by
  refine ⟨x₁, Int.cast (2 : Int) * x₁, _, _, ?_, ?_, rfl, rfl, ?_⟩ <;> ext <;> simp [x₁]

/-- **Theorem B needs `NonSquare d₂`.** With `(d₁, d₂) = (2, 4)` (product 8 is
    a non-square) take `t = 2`. Then walker 2's phase is the constant 2, and the
    rule `θ₂ = 0·θ₁ + 2` holds at tick 1. -/
theorem no_direct_rule_needs_second :
    ∃ s t θ₁ θ₂ : Inst 2 4,
      s * s = Int.cast ((2 : Nat) : Int) ∧ t * t = Int.cast ((4 : Nat) : Int) ∧
      θ₁ = Int.cast (1 : Int) * s - Int.cast (0 : Int) ∧
      θ₂ = Int.cast (1 : Int) * t - Int.cast (0 : Int) ∧
      Int.cast (1 : Int) * θ₂ = Int.cast (0 : Int) * θ₁ + Int.cast (2 : Int) := by
  refine ⟨x₁, Int.cast (2 : Int), _, _, ?_, ?_, rfl, rfl, ?_⟩ <;> ext <;> simp [x₁]

/-- **Full independence needs `NonSquare d₁`.** With `(d₁, d₂) = (4, 2)` (`d₂`
    and the product 8 are non-squares) take `s = 2`: then `−2 + 1·s − 0·t = 0`
    with a nonzero coefficient. -/
theorem independent_needs_first :
    ∃ s t : Inst 4 2, s * s = Int.cast ((4 : Nat) : Int) ∧ t * t = Int.cast ((2 : Nat) : Int) ∧
      Int.cast (-2 : Int) + Int.cast (1 : Int) * s - Int.cast (0 : Int) * t = (0 : Inst 4 2) ∧
      (1 : Int) ≠ 0 := by
  refine ⟨Int.cast (2 : Int), x₂, ?_, ?_, ?_, by decide⟩ <;> ext <;> simp [x₂]

end SimulationExchange
