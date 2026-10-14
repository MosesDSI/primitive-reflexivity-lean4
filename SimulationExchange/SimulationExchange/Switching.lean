/-
  Switching.lean — the four worlds as column sign-flips on the instructure model.

  An element of `Inst d₁ d₂` is `a + b·x₁ + c·x₂ + e·x₁x₂`, stored as four
  integers. A world is a choice of sign for each generator, i.e. two bits
  `(p, q)`. The switch `switch p q` negates `b` when `p`, `c` when `q`, and
  `e` when exactly one of them is set. This is the table of Section 4.1 of
  "Two Walkers and a Tick":

      switch            a   b   c   e
      (false,false) id  +   +   +   +
      (true, false) σ   +   −   +   −
      (false,true)  τ   +   +   −   −
      (true, true)  π   +   −   −   +

  §19  Each switch is a ring map (additive, multiplicative, fixes 1 and the
       integers) and sends each generator to ± itself.
  §20  Switches commute with walkers and leave the tick alone; they compose by
       XOR on the two bits; each undoes itself; the four are distinct.
  §21  Fixed sets: π fixes exactly b = c = 0, σ exactly b = e = 0, τ exactly
       c = e = 0; among the four, the ones fixing x₁x₂ are exactly id and π.
  §22  The table is forced: any additive map with f 1 = 1, sending x₁ ↦ ±x₁,
       x₂ ↦ ±x₂, and respecting the one product x₁·x₂, IS the corresponding
       switch. The e-column sign is a consequence, not a choice.
  §23  Necessity of every hypothesis of §22, and non-vacuity.

  None of §19–§21 needs any hypothesis on d₁, d₂: the table holds in the
  integer model for every pair.
-/
import SimulationExchange.Core
import SimulationExchange.Model

open Lean.Grind

namespace SimulationExchange
namespace Inst
variable {d₁ d₂ : Int}

/-! ## §19  Switches are ring maps -/

/-- The sign attached to a bit: `true ↦ −1`, `false ↦ 1`. -/
def sgn (p : Bool) : Int := if p then -1 else 1

/-- The switch to world `(p, q)`: negate `b` if `p`, `c` if `q`, `e` if `p xor q`. -/
def switch (p q : Bool) (x : Inst d₁ d₂) : Inst d₁ d₂ :=
  ⟨x.a, sgn p * x.b, sgn q * x.c, sgn (p ^^ q) * x.e⟩

theorem switch_add (p q : Bool) (x y : Inst d₁ d₂) :
    switch p q (x + y) = switch p q x + switch p q y := by
  ext <;> cases p <;> cases q <;> simp [switch, sgn] <;> omega

theorem switch_mul (p q : Bool) (x y : Inst d₁ d₂) :
    switch p q (x * y) = switch p q x * switch p q y := by
  ext <;> cases p <;> cases q <;> simp [switch, sgn] <;> grind

theorem switch_one (p q : Bool) : switch p q (1 : Inst d₁ d₂) = 1 := by
  ext <;> simp [switch]

/-- **The tick is left alone**: every switch fixes the integers. -/
theorem switch_intCast (p q : Bool) (n : Int) :
    switch p q ((n : Int) : Inst d₁ d₂) = (n : Inst d₁ d₂) := by
  ext <;> simp [switch]

theorem switch_x₁ (p q : Bool) :
    switch p q (x₁ : Inst d₁ d₂) = ((sgn p : Int) : Inst d₁ d₂) * x₁ := by
  ext <;> cases p <;> simp [switch, sgn, x₁]

theorem switch_x₂ (p q : Bool) :
    switch p q (x₂ : Inst d₁ d₂) = ((sgn q : Int) : Inst d₁ d₂) * x₂ := by
  ext <;> cases q <;> simp [switch, sgn, x₂]

/-! ## §20  Commuting, composing, undoing, distinct -/

/-- **Switches commute with walkers.** Switching the walker `n·x₁ − k`
    gives the walker with the flipped generator, at the same tick `n`
    and the same offset `k`. -/
theorem switch_walker (p q : Bool) (n k : Int) :
    switch p q ((n : Inst d₁ d₂) * x₁ - (k : Inst d₁ d₂))
      = (n : Inst d₁ d₂) * (((sgn p : Int) : Inst d₁ d₂) * x₁) - (k : Inst d₁ d₂) := by
  ext <;> cases p <;> simp [switch, sgn, x₁]

/-- **Composition is XOR on the two bits.** -/
theorem switch_switch (p q p' q' : Bool) (x : Inst d₁ d₂) :
    switch p q (switch p' q' x) = switch (p ^^ p') (q ^^ q') x := by
  ext <;> cases p <;> cases q <;> cases p' <;> cases q' <;> simp [switch, sgn]

theorem switch_id (x : Inst d₁ d₂) : switch false false x = x := by
  ext <;> simp [switch, sgn]

/-- **Every switch undoes itself.** -/
theorem switch_involutive (p q : Bool) (x : Inst d₁ d₂) :
    switch p q (switch p q x) = x := by
  rw [switch_switch]; simp [switch_id]

/-- σ then τ is π. -/
theorem sigma_tau_eq_pi (x : Inst d₁ d₂) :
    switch true false (switch false true x) = switch true true x := by
  rw [switch_switch]; rfl

/-- **The four switches are distinct**: a switch is determined by its bits. -/
theorem switch_inj (p q p' q' : Bool)
    (h : ∀ x : Inst d₁ d₂, switch p q x = switch p' q' x) : p = p' ∧ q = q' := by
  have h1 := congrArg Inst.b (h x₁)
  have h2 := congrArg Inst.c (h x₂)
  cases p <;> cases p' <;> cases q <;> cases q' <;> simp [switch, sgn, x₁, x₂] at h1 h2 ⊢

/-! ## §21  Fixed sets -/

/-- **π fixes exactly the elements `a + e·x₁x₂`**: the integer form of
    the Phantom Middle's fixed field. -/
theorem pi_fixed_iff (x : Inst d₁ d₂) : switch true true x = x ↔ x.b = 0 ∧ x.c = 0 := by
  constructor
  · intro h
    have hb := congrArg Inst.b h
    have hc := congrArg Inst.c h
    simp [switch, sgn] at hb hc
    omega
  · rintro ⟨hb, hc⟩
    ext <;> simp [switch, sgn, hb, hc]

/-- σ fixes exactly the elements `a + c·x₂`. -/
theorem sigma_fixed_iff (x : Inst d₁ d₂) : switch true false x = x ↔ x.b = 0 ∧ x.e = 0 := by
  constructor
  · intro h
    have hb := congrArg Inst.b h
    have he := congrArg Inst.e h
    simp [switch, sgn] at hb he
    omega
  · rintro ⟨hb, he⟩
    ext <;> simp [switch, sgn, hb, he]

/-- τ fixes exactly the elements `a + b·x₁`. -/
theorem tau_fixed_iff (x : Inst d₁ d₂) : switch false true x = x ↔ x.c = 0 ∧ x.e = 0 := by
  constructor
  · intro h
    have hc := congrArg Inst.c h
    have he := congrArg Inst.e h
    simp [switch, sgn] at hc he
    omega
  · rintro ⟨hc, he⟩
    ext <;> simp [switch, sgn, hc, he]

/-- **Among the four switches, exactly id and π fix `x₁·x₂`.** -/
theorem switch_fixes_prod_iff (p q : Bool) :
    switch p q ((x₁ : Inst d₁ d₂) * x₂) = x₁ * x₂ ↔ p = q := by
  cases p <;> cases q <;> simp [switch, sgn, x₁, x₂, Inst.ext_iff]

/-! ## §22  The table is forced -/

/-- An additive map on `Inst` commutes with integer multiples. -/
theorem additive_intCast_mul (f : Inst d₁ d₂ → Inst d₁ d₂)
    (hadd : ∀ x y, f (x + y) = f x + f y) (n : Int) (y : Inst d₁ d₂) :
    f ((n : Inst d₁ d₂) * y) = (n : Inst d₁ d₂) * f y := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [show (0 : Inst d₁ d₂) + 0 = 0 by ext <;> simp] at h
    ext
    · have := congrArg Inst.a h; simp at this; simp; omega
    · have := congrArg Inst.b h; simp at this; simp; omega
    · have := congrArg Inst.c h; simp at this; simp; omega
    · have := congrArg Inst.e h; simp at this; simp; omega
  have hnat : ∀ k : Nat, f (((k : Int) : Inst d₁ d₂) * y) = ((k : Int) : Inst d₁ d₂) * f y := by
    intro k
    induction k with
    | zero =>
      rw [show ((((0 : Nat) : Int)) : Inst d₁ d₂) * y = 0 by ext <;> simp, h0]
      ext <;> simp
    | succ k ih =>
      rw [show ((((k + 1 : Nat) : Int)) : Inst d₁ d₂) * y = ((k : Int) : Inst d₁ d₂) * y + y by
            ext <;> simp <;> grind,
          hadd, ih]
      ext <;> simp <;> grind
  have hneg : ∀ z : Inst d₁ d₂, f (-z) = -f z := by
    intro z
    have h := hadd z (-z)
    rw [show z + -z = 0 by ext <;> simp <;> omega, h0] at h
    ext
    · have := congrArg Inst.a h; simp at this; simp; omega
    · have := congrArg Inst.b h; simp at this; simp; omega
    · have := congrArg Inst.c h; simp at this; simp; omega
    · have := congrArg Inst.e h; simp at this; simp; omega
  cases n with
  | ofNat k => exact hnat k
  | negSucc k =>
    rw [show ((Int.negSucc k : Int) : Inst d₁ d₂) * y = -((((k + 1 : Nat) : Int) : Inst d₁ d₂) * y) by
          ext <;> simp [Int.negSucc_eq] <;> grind,
        hneg, hnat]
    ext <;> simp [Int.negSucc_eq] <;> grind

/-- **The switching table is forced.** Any map that is additive, fixes 1,
    sends `x₁ ↦ sgn p · x₁` and `x₂ ↦ sgn q · x₂`, and respects the single
    product `x₁ · x₂`, is exactly `switch p q`. In particular the sign of the
    `e` column is determined by multiplication, not chosen. -/
theorem switch_unique (p q : Bool) (f : Inst d₁ d₂ → Inst d₁ d₂)
    (hadd : ∀ x y, f (x + y) = f x + f y) (h1 : f 1 = 1)
    (hx₁ : f x₁ = ((sgn p : Int) : Inst d₁ d₂) * x₁)
    (hx₂ : f x₂ = ((sgn q : Int) : Inst d₁ d₂) * x₂)
    (hprod : f (x₁ * x₂) = f x₁ * f x₂) :
    ∀ x, f x = switch p q x := by
  intro x
  have hx : x = ((x.a : Int) : Inst d₁ d₂) * 1 + ((x.b : Int) : Inst d₁ d₂) * x₁
      + ((x.c : Int) : Inst d₁ d₂) * x₂ + ((x.e : Int) : Inst d₁ d₂) * (x₁ * x₂) := by
    ext <;> simp [x₁, x₂]
  rw [hx, hadd, hadd, hadd, additive_intCast_mul f hadd, additive_intCast_mul f hadd,
    additive_intCast_mul f hadd, additive_intCast_mul f hadd, h1, hprod, hx₁, hx₂]
  ext <;> cases p <;> cases q <;> simp [switch, sgn, x₁, x₂]

/-! ## §23  Necessity and non-vacuity -/

/-- **Non-vacuity.** Every switch satisfies every hypothesis of `switch_unique`
    (shown in the trap's own model `Inst 30 33`). -/
theorem switch_satisfies_hypotheses (p q : Bool) :
    (∀ x y : Inst 30 33, switch p q (x + y) = switch p q x + switch p q y) ∧
    switch p q (1 : Inst 30 33) = 1 ∧
    switch p q (x₁ : Inst 30 33) = ((sgn p : Int) : Inst 30 33) * x₁ ∧
    switch p q (x₂ : Inst 30 33) = ((sgn q : Int) : Inst 30 33) * x₂ ∧
    switch p q ((x₁ : Inst 30 33) * x₂) = switch p q x₁ * switch p q x₂ :=
  ⟨switch_add p q, switch_one p q, switch_x₁ p q, switch_x₂ p q, switch_mul p q x₁ x₂⟩

/-- Negate the `b` column only: additive, fixes 1 and both generators' images
    as σ does, but does not respect `x₁·x₂`. -/
def negBOnly (x : Inst 2 3) : Inst 2 3 := ⟨x.a, -x.b, x.c, x.e⟩

/-- **`hprod` is needed.** `negBOnly` satisfies every other hypothesis for σ
    yet differs from σ on `x₁·x₂`: without the product rule, the `e` column
    is not forced. -/
theorem switch_unique_needs_prod :
    (∀ x y, negBOnly (x + y) = negBOnly x + negBOnly y) ∧ negBOnly 1 = 1 ∧
    negBOnly x₁ = ((sgn true : Int) : Inst 2 3) * x₁ ∧
    negBOnly x₂ = ((sgn false : Int) : Inst 2 3) * x₂ ∧
    negBOnly (x₁ * x₂) ≠ switch true false (x₁ * x₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; ext <;> simp [negBOnly] <;> omega
  · ext <;> simp [negBOnly]
  · ext <;> simp [negBOnly, sgn, x₁]
  · ext <;> simp [negBOnly, sgn, x₂]
  · intro h; have := congrArg Inst.e h; simp [negBOnly, switch, sgn, x₁, x₂] at this

/-- σ plus a non-additive correction that vanishes on 1, on both generators
    and on their product, and commutes with integer scaling. -/
def sigmaBent (x : Inst 2 3) : Inst 2 3 :=
  ⟨x.a, -x.b, x.c, -x.e + (if x.b ≠ 0 then x.a else 0)⟩

/-- **`hadd` is needed.** `sigmaBent` fixes 1, sends the generators as σ does,
    and respects `x₁·x₂`, yet differs from σ at `1 + x₁`. -/
theorem switch_unique_needs_add :
    sigmaBent 1 = 1 ∧
    sigmaBent x₁ = ((sgn true : Int) : Inst 2 3) * x₁ ∧
    sigmaBent x₂ = ((sgn false : Int) : Inst 2 3) * x₂ ∧
    sigmaBent (x₁ * x₂) = sigmaBent x₁ * sigmaBent x₂ ∧
    sigmaBent (1 + x₁) ≠ switch true false (1 + x₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [sigmaBent]
  · ext <;> simp [sigmaBent, sgn, x₁]
  · ext <;> simp [sigmaBent, sgn, x₂]
  · ext <;> simp [sigmaBent, x₁, x₂]
  · intro h; have := congrArg Inst.e h; simp [sigmaBent, switch, sgn, x₁] at this

/-- σ plus the `a` coordinate copied into itself: additive, correct on both
    generators and on their product, but sends 1 to 2. -/
def sigmaDoubled (x : Inst 2 3) : Inst 2 3 := ⟨2 * x.a, -x.b, x.c, -x.e⟩

/-- **`h1` is needed.** -/
theorem switch_unique_needs_one :
    (∀ x y, sigmaDoubled (x + y) = sigmaDoubled x + sigmaDoubled y) ∧
    sigmaDoubled x₁ = ((sgn true : Int) : Inst 2 3) * x₁ ∧
    sigmaDoubled x₂ = ((sgn false : Int) : Inst 2 3) * x₂ ∧
    sigmaDoubled (x₁ * x₂) = sigmaDoubled x₁ * sigmaDoubled x₂ ∧
    sigmaDoubled 1 ≠ switch true false 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; ext <;> simp [sigmaDoubled] <;> omega
  · ext <;> simp [sigmaDoubled, sgn, x₁]
  · ext <;> simp [sigmaDoubled, sgn, x₂]
  · ext <;> simp [sigmaDoubled, x₁, x₂]
  · intro h; have := congrArg Inst.a h; simp [sigmaDoubled, switch] at this

/-- **`hx₁` is needed.** The identity satisfies every other hypothesis for σ
    (`q = false`) but is not σ. -/
theorem switch_unique_needs_x₁ :
    (id : Inst 2 3 → Inst 2 3) x₂ = ((sgn false : Int) : Inst 2 3) * x₂ ∧
    (id : Inst 2 3 → Inst 2 3) x₁ ≠ switch true false x₁ := by
  refine ⟨?_, ?_⟩
  · ext <;> simp [sgn, x₂]
  · intro h; have := congrArg Inst.b h; simp [switch, sgn, x₁] at this

/-- **`hx₂` is needed.** The identity satisfies every other hypothesis for τ
    (`p = false`) but is not τ. -/
theorem switch_unique_needs_x₂ :
    (id : Inst 2 3 → Inst 2 3) x₁ = ((sgn false : Int) : Inst 2 3) * x₁ ∧
    (id : Inst 2 3 → Inst 2 3) x₂ ≠ switch false true x₂ := by
  refine ⟨?_, ?_⟩
  · ext <;> simp [sgn, x₁]
  · intro h; have := congrArg Inst.c h; simp [switch, sgn, x₂] at this

/-- The table at the trap: π fixes the mixed generator `x₁x₂` (√990 in the
    real picture) and negates both walkers. -/
theorem trap_pi_table :
    switch true true ((x₁ : Inst 30 33) * x₂) = x₁ * x₂ ∧
    switch true true (x₁ : Inst 30 33) = -x₁ ∧
    switch true true (x₂ : Inst 30 33) = -x₂ := by
  refine ⟨(switch_fixes_prod_iff true true).mpr rfl, ?_, ?_⟩ <;>
    ext <;> simp [switch, sgn, x₁, x₂]

end Inst
end SimulationExchange
