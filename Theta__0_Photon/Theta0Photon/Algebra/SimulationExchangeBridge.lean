import Theta0Photon.Algebra.GeneralFieldTower
import SimulationExchange

/-!
# Simulation Exchange, Mathlib bridge: `R = ℝ`, `s = √d₁`, `t = √d₂`

`SimulationExchange/` (a standalone bare-Lean Lake package, no Mathlib — see
its own build summary) proves Theorem A (`faithful`, simulation condition S2)
and Theorem B (`no_direct_rule`) for an arbitrary characteristic-0 commutative
ring `R` containing square roots of `d₁, d₂`. This file carries out that
package's handoff task 3: instantiate both theorems at `R = ℝ`,
`s = Real.sqrt d₁`, `t = Real.sqrt d₂`; connect `SimulationExchange.NonSquare`
to the `¬ IsSquare` hypotheses `GeneralFieldTower.lean` already uses; state
the `Int.fract` corollaries matching `Simulation_Formal_Definition.md`'s S2
row; and cross-check `no_direct_rule` at `ℝ` against
`GeneralFieldTower.sqrt_notMem` without re-proving it.

Confirmed first, interactively, against this project's pinned `v4.33.1`
toolchain and Mathlib revision: `ℝ` resolves both `Lean.Grind.CommRing ℝ` and
`Lean.Grind.IsCharP ℝ 0` (`#check (inferInstance : Lean.Grind.CommRing ℝ)` and
the `IsCharP` analogue both elaborate with no extra instances needed), so
`SimulationExchange.faithful` and `.no_direct_rule` apply to `R = ℝ` directly.
-/

open Polynomial IntermediateField

noncomputable section

namespace Theta0Photon.SimulationExchangeBridge

/-- Bridge between `SimulationExchange.NonSquare` (`∀ r, r·r ≠ d`) and
Mathlib's `IsSquare`, in the same spirit as `GeneralFieldTower`'s
`not_exists_sq_of_not_isSquare` / `not_isSquare_of_not_exists_sq`, stated here
as a single `iff` since the two forms are interchangeable by pure logic (no
extra hypothesis needed in either direction). -/
theorem nonSquare_iff_not_isSquare (d : ℕ) :
    SimulationExchange.NonSquare d ↔ ¬ IsSquare d := by
  constructor
  · intro hd hsq
    obtain ⟨r, hr⟩ := hsq
    exact hd r hr.symm
  · intro hd r hr
    exact hd ⟨r, hr.symm⟩

/-- `Real.sqrt d` squares to `d`, cast exactly as `SimulationExchange.faithful`
and `.no_direct_rule` expect it (`Int.cast (d : ℤ)`, not the plain `ℕ`-cast). -/
theorem sqrt_sq_intCast (d : ℕ) :
    Real.sqrt d * Real.sqrt d = (Int.cast (d : ℤ) : ℝ) := by
  rw [Real.mul_self_sqrt (Nat.cast_nonneg d)]
  norm_num

/-! ## Theorem A and B, instantiated at `R = ℝ` -/

/-- **Theorem A (faithfulness, S2) at `R = ℝ`.** Two carrier ticks that
render walker 1 (`s = √d`) to an integer-displaced phase are equal — for
*every* non-square `d`, not just the trap's `d = 30`. -/
theorem faithful_real {d : ℕ} (hd : ¬ IsSquare d) (n m j : ℤ)
    (h : (Int.cast (n - m) : ℝ) * Real.sqrt d = (Int.cast j : ℝ)) : n = m :=
  SimulationExchange.faithful ((nonSquare_iff_not_isSquare d).mpr hd)
    (Real.sqrt d) (sqrt_sq_intCast d) n m j h

/-- **Theorem B (no direct rule) at `R = ℝ`.** At no tick `n ≥ 1` is
walker 2's phase (`t = √d₂`) a rational-affine function of walker 1's
(`s = √d₁`), for any integer offsets `k₁, k₂`. -/
theorem no_direct_rule_real {d₁ d₂ : ℕ} (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) (n v u w k₁ k₂ : ℤ) (hn : 1 ≤ n) (hv : 1 ≤ v)
    (θ₁ θ₂ : ℝ) (e₁ : θ₁ = Int.cast n * Real.sqrt d₁ - Int.cast k₁)
    (e₂ : θ₂ = Int.cast n * Real.sqrt d₂ - Int.cast k₂)
    (rule : Int.cast v * θ₂ = Int.cast u * θ₁ + (Int.cast w : ℝ)) : False :=
  SimulationExchange.no_direct_rule ((nonSquare_iff_not_isSquare d₂).mpr hd2)
    ((nonSquare_iff_not_isSquare (d₁ * d₂)).mpr hd12)
    (Real.sqrt d₁) (Real.sqrt d₂) (sqrt_sq_intCast d₁) (sqrt_sq_intCast d₂)
    n v u w k₁ k₂ hn hv θ₁ θ₂ e₁ e₂ rule

/-! ## `Int.fract` corollaries, matching `Simulation_Formal_Definition.md`'s
S2 row -/

/-- **S2, stated with `Int.fract`.** Two carrier ticks whose walker-1
renderings have the same fractional part are equal. -/
theorem fract_faithful {d : ℕ} (hd : ¬ IsSquare d) (n m : ℤ)
    (h : Int.fract ((n : ℝ) * Real.sqrt d) = Int.fract ((m : ℝ) * Real.sqrt d)) :
    n = m := by
  simp only [Int.fract] at h
  apply faithful_real hd n m (⌊(n : ℝ) * Real.sqrt d⌋ - ⌊(m : ℝ) * Real.sqrt d⌋)
  push_cast
  linear_combination h

/-- **Theorem B's analogue for `Int.fract`.** For any tick `n ≥ 1` and any
rationals `p, q`, walker 2's fractional phase is never `p` times walker 1's
plus `q`. Clears the denominators of `p, q` into the integer `(v, u, w)` that
`no_direct_rule_real` already rules out. -/
theorem fract_no_direct_rule {d₁ d₂ : ℕ} (hd2 : ¬ IsSquare d₂)
    (hd12 : ¬ IsSquare (d₁ * d₂)) (n : ℤ) (hn : 1 ≤ n) (p q : ℚ) :
    Int.fract ((n : ℝ) * Real.sqrt d₂)
      ≠ p * Int.fract ((n : ℝ) * Real.sqrt d₁) + q := by
  intro h
  have hpd : 1 ≤ (p.den : ℤ) := by exact_mod_cast p.pos
  have hqd : 1 ≤ (q.den : ℤ) := by exact_mod_cast q.pos
  have hpd' : (p.den : ℝ) ≠ 0 := by exact_mod_cast p.den_nz
  have hqd' : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  refine no_direct_rule_real hd2 hd12 n (p.den * q.den : ℤ) (p.num * q.den : ℤ)
    (q.num * p.den : ℤ) ⌊(n : ℝ) * Real.sqrt d₁⌋ ⌊(n : ℝ) * Real.sqrt d₂⌋ hn
    (by nlinarith) (Int.fract ((n : ℝ) * Real.sqrt d₁)) (Int.fract ((n : ℝ) * Real.sqrt d₂))
    (by simp only [Int.fract]) (by simp only [Int.fract]) ?_
  rw [h]
  push_cast
  rw [Rat.cast_def, Rat.cast_def]
  field_simp

/-! ## Cross-check against `GeneralFieldTower.sqrt_notMem` -/

/-- **Consistency check, not a new proof of `sqrt_notMem`.** If
`√d₂ ∈ ℚ⟮√d₁⟯` — the negation of `GeneralFieldTower.sqrt_notMem`'s conclusion
— then clearing denominators in the resulting `√d₂ = a + c·√d₁` (rationals
`a, c`, from `sqrt_field_eq`) produces exactly the integer affine rule
`v·√d₂ = u·√d₁ + w` (`v ≥ 1`) that `no_direct_rule_real` forbids at tick
`n = 1`, offsets `k₁ = k₂ = 0`. This route never calls `sqrt_notMem` itself —
it reaches the same conclusion through the bare-Lean package's
`descent`/`norm_identity` argument instead of the field-theoretic one,
confirming the two trees agree. -/
theorem sqrt_notMem_agrees_with_no_direct_rule {d₁ d₂ : ℕ}
    (hd1 : ¬ IsSquare d₁) (hd2 : ¬ IsSquare d₂) (hd12 : ¬ IsSquare (d₁ * d₂)) :
    Real.sqrt d₂ ∉ (ℚ⟮Real.sqrt (d₁ : ℝ)⟯ : IntermediateField ℚ ℝ) := by
  intro hmem
  obtain ⟨a, c, hac⟩ :=
    Theta0Photon.GeneralFieldTower.sqrt_field_eq hd1
      (⟨Real.sqrt d₂, hmem⟩ : ℚ⟮Real.sqrt (d₁ : ℝ)⟯)
  have hac' : Real.sqrt (d₂ : ℝ) = (a : ℝ) + (c : ℝ) * Real.sqrt d₁ := hac
  have had : 1 ≤ (a.den : ℤ) := by exact_mod_cast a.pos
  have hcd : 1 ≤ (c.den : ℤ) := by exact_mod_cast c.pos
  have had' : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
  have hcd' : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_nz
  exact no_direct_rule_real hd2 hd12 1 (a.den * c.den : ℤ) (c.num * a.den : ℤ)
    (a.num * c.den : ℤ) 0 0 (le_refl 1) (by nlinarith)
    (Real.sqrt d₁) (Real.sqrt d₂) (by push_cast; ring) (by push_cast; ring)
    (by rw [hac']; push_cast; rw [Rat.cast_def, Rat.cast_def]; field_simp; ring)

end Theta0Photon.SimulationExchangeBridge

end

#print axioms Theta0Photon.SimulationExchangeBridge.nonSquare_iff_not_isSquare
#print axioms Theta0Photon.SimulationExchangeBridge.faithful_real
#print axioms Theta0Photon.SimulationExchangeBridge.no_direct_rule_real
#print axioms Theta0Photon.SimulationExchangeBridge.fract_faithful
#print axioms Theta0Photon.SimulationExchangeBridge.fract_no_direct_rule
#print axioms Theta0Photon.SimulationExchangeBridge.sqrt_notMem_agrees_with_no_direct_rule
