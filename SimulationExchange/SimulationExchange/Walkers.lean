/-
  Walkers.lean — two short consequences of the general descent.

  §9  Coincidence only at the origin (walk/fall Proposition 1).
      Two walkers: the Polar walker takes rational steps of length `c`
      (the Manhattan step, `c = 2` on the unit square), the Axial walker takes
      steps `s` with `s·s = d` (the diagonal step, `d = 2`). Their pair
      `(c·m, n·s)` lies on the main diagonal `D1` — the fall `F` vanishes —
      exactly when `c·m = n·s`. That happens only at the origin.

  §10 Dominance never ties.
      In a mixture `z = b·s + c·t` of both walkers, the dominance quantity
      `z · τ(z) = (b·s + c·t)(b·s − c·t)` equals the integer `b²·d₁ − c²·d₂`,
      whatever square roots are chosen (so in every orientation), and it is
      zero only for the empty mixture.
-/
import SimulationExchange.Core
import SimulationExchange.Model

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange

/-! ## §9  Coincidence only at the origin -/

/-- **Proposition 1 (coincidence only at the origin).** In a commutative ring
    of characteristic 0 with `s·s = d`, `d` a non-square, and a nonzero
    rational step `c`: if `m` Polar steps and `n` Axial steps land the pair on
    the diagonal (`c·m = n·s`), then `m = n = 0`. -/
theorem coincidence_only_at_origin {R : Type} [CommRing R] [IsCharP R 0]
    {d : Nat} (hd : NonSquare d) (s : R) (hs : s * s = Int.cast (d : Int))
    (c : Int) (hc : c ≠ 0) (m n : Int)
    (h : (Int.cast (c * m) : R) = Int.cast n * s) : m = 0 ∧ n = 0 := by
  have hR : (Int.cast (n * n * (d : Int) - (c * m) * (c * m)) : R) = 0 := by grind
  have hZ := int_eq_zero_of_cast _ hR
  have hn : n = 0 := descent_int hd n (c * m) (by omega)
  subst hn
  have hcm : (Int.cast (c * m) : R) = 0 := by rw [h]; grind
  have hcm0 := int_eq_zero_of_cast _ hcm
  rcases Int.mul_eq_zero.mp hcm0 with h0 | h0
  · exact absurd h0 hc
  · exact ⟨h0, rfl⟩

/-- The paper's case: Manhattan step `2`, diagonal step `s` with `s·s = 2`. -/
theorem walkers_coincide_only_at_origin {R : Type} [CommRing R] [IsCharP R 0]
    (s : R) (hs : s * s = Int.cast ((2 : Nat) : Int)) (m n : Int)
    (h : (Int.cast (2 * m) : R) = Int.cast n * s) : m = 0 ∧ n = 0 :=
  coincidence_only_at_origin nonSquare_2 s hs 2 (by decide) m n h

/-! ## §10  Dominance never ties -/

/-- **Dominance identity.** For any square roots `s, t` of `d₁, d₂` (any signs,
    so in every orientation), `(b·s + c·t)(b·s − c·t) = b²·d₁ − c²·d₂`. -/
theorem dominance_identity {R : Type} [CommRing R] (s t : R) (d₁ d₂ b c : Int)
    (hs : s * s = Int.cast d₁) (ht : t * t = Int.cast d₂) :
    (Int.cast b * s + Int.cast c * t) * (Int.cast b * s - Int.cast c * t)
      = (Int.cast (b * b * d₁ - c * c * d₂) : R) := by
  grind

/-- **Integer core: no tie.** If `d₁·d₂` is a non-square then
    `b²·d₁ = c²·d₂` forces `b = c = 0`. This single hypothesis suffices:
    it already rules out `d₁ = 0` and `d₂ = 0`. -/
theorem no_tie {d₁ d₂ : Nat} (h₁₂ : NonSquare (d₁ * d₂)) (b c : Int)
    (h : b * b * (d₁ : Int) = c * c * (d₂ : Int)) : b = 0 ∧ c = 0 := by
  have hd₁ : (d₁ : Int) ≠ 0 := by
    intro h0
    have : d₁ = 0 := by omega
    exact h₁₂ 0 (by subst this; simp)
  -- multiply by d₁:  (b·d₁)² = c²·(d₁d₂)
  have hc : c = 0 := descent_int h₁₂ c (b * d₁) (by push_cast; grind)
  subst hc
  have : b * b * (d₁ : Int) = 0 := by grind
  have hbb : b * b = 0 := by
    rcases Int.mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hd₁
  exact ⟨int_mul_self_eq_zero hbb, rfl⟩

/-- **Dominance never ties.** In a commutative ring of characteristic 0,
    a mixture whose dominance quantity vanishes is the empty mixture. -/
theorem dominance_never_ties {R : Type} [CommRing R] [IsCharP R 0]
    {d₁ d₂ : Nat} (h₁₂ : NonSquare (d₁ * d₂))
    (s t : R) (hs : s * s = Int.cast (d₁ : Int)) (ht : t * t = Int.cast (d₂ : Int))
    (b c : Int)
    (h : (Int.cast b * s + Int.cast c * t) * (Int.cast b * s - Int.cast c * t) = (0 : R)) :
    b = 0 ∧ c = 0 := by
  have hid := dominance_identity s t d₁ d₂ b c hs ht
  rw [h] at hid
  have hZ := int_eq_zero_of_cast _ hid.symm
  exact no_tie h₁₂ b c (by omega)

/-! ## §11  Instances in the model and necessity -/

open Inst

/-- Proposition 1 inside the instructure model `ℤ[x₁, x₂]/(x₁² − 2, x₂² − 3)`. -/
theorem model_walkers_coincide_only_at_origin (m n : Int)
    (h : (Int.cast (2 * m) : Inst 2 3) = Int.cast n * x₁) : m = 0 ∧ n = 0 :=
  walkers_coincide_only_at_origin x₁ x₁_sq m n h

/-- Dominance never ties for the trap `(30, 33)`, inside its own model. -/
theorem trap_dominance_never_ties (b c : Int)
    (h : (Int.cast b * (x₁ : Inst 30 33) + Int.cast c * x₂)
          * (Int.cast b * x₁ - Int.cast c * x₂) = 0) : b = 0 ∧ c = 0 :=
  dominance_never_ties (d₁ := 30) (d₂ := 33) nonSquare_990 x₁ x₂ x₁_sq x₂_sq b c h

/-- **Proposition 1 needs `NonSquare d`.** With `d = 4`, `s = 2`, `c = 2`:
    one step each lands on the diagonal (`2·1 = 1·2`). -/
theorem coincidence_needs_nonSquare :
    ∃ s : Inst 4 3, s * s = Int.cast ((4 : Nat) : Int) ∧
      (Int.cast ((2 : Int) * 1) : Inst 4 3) = Int.cast (1 : Int) * s :=
  ⟨Int.cast (2 : Int), by ext <;> simp, by ext <;> simp⟩

/-- **Proposition 1 needs `c ≠ 0`.** With `c = 0`, `m = 1`, `n = 0` the
    equation `c·m = n·s` holds although `m ≠ 0`. -/
theorem coincidence_needs_step :
    (Int.cast ((0 : Int) * 1) : Inst 2 3) = Int.cast (0 : Int) * x₁ := by
  ext <;> simp [x₁]

/-- **No tie needs `NonSquare (d₁·d₂)`.** With `(d₁, d₂) = (2, 8)` (product
    16): `b = 2`, `c = 1` gives `2²·2 = 1²·8`. -/
theorem no_tie_needs_product : (2 : Int) * 2 * 2 = 1 * 1 * 8 := by decide

/-- **Dominance-never-ties needs `NonSquare (d₁·d₂)`, at the ring level.**
    In `Inst 2 8` take `s = x₁` and `t = 2·x₁` (so `t·t = 8`). Then the mixture
    with `b = 2`, `c = 1` has vanishing dominance quantity although `b ≠ 0`. -/
theorem dominance_needs_product :
    ∃ s t : Inst 2 8, s * s = Int.cast ((2 : Nat) : Int) ∧ t * t = Int.cast ((8 : Nat) : Int) ∧
      (Int.cast (2 : Int) * s + Int.cast (1 : Int) * t)
        * (Int.cast (2 : Int) * s - Int.cast (1 : Int) * t) = 0 ∧ (2 : Int) ≠ 0 := by
  refine ⟨x₁, Int.cast (2 : Int) * x₁, ?_, ?_, ?_, by decide⟩ <;> ext <;> simp [x₁]

end SimulationExchange
