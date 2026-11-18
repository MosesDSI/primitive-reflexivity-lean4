/-!
# ZeroGrind — zero-axiom lemmas for core's `Lean.Grind` ring classes

SimulationExchange states its walker algebra for any `Lean.Grind.CommRing R`
with `Lean.Grind.IsCharP R 0`. The class *fields* (`add_comm`, `left_distrib`,
`neg_add_cancel`, `intCast_neg`, `IsCharP.ofNat_ext_iff`, ...) depend on no
axioms, but several of core's *derived* lemmas do:

* `Lean.Grind.Ring.neg_mul`, `Ring.intCast_add`, `Ring.intCast_mul`:
  `[propext, Quot.sound]`;
* `Lean.Grind.IsCharP.intCast_eq_zero_iff`: `[propext, Classical.choice, Quot.sound]`;
* and, underneath, `Nat.mod_zero` (`x % 0 = x`): `[propext]`.

This module re-derives what SimulationExchange needs from the fields alone.

Hygiene: no `simp`, `omega`, `decide`, `by_cases` or `grind`, no Nat
subtraction. Proofs are terms built from the class fields, `Eq.trans`,
`Eq.symm`, `congrArg`, and `rw` with definitional unfoldings
(`Nat.mod.eq_def`, `Nat.modCore.eq_def`). Target: zero axioms for every
declaration.

Increment 0 contents.

* `mod_zero'`: `x % 0 = x`, axiom-free (core's `Nat.mod_zero` uses `propext`).
* Additive lemmas from the fields: `zero_add`, `add_left_comm`, `neg_eq_zero`.
* `ofNat_add`: numerals add, by induction on the field `ofNat_succ`.
* The `IsCharP` test: `ofNat_eq_zero_of_charZero` and `int_eq_zero_of_cast`,
  the latter with exactly the statement of `SimulationExchange.int_eq_zero_of_cast`.
  Characteristic 0 is read through the single class field
  `ofNat_ext_iff : OfNat.ofNat x = OfNat.ofNat y ↔ x % 0 = y % 0`.

Further lemmas (`neg_mul`, `intCast_add`, `intCast_mul`, ...) are added in the
increment that first needs them.
-/

set_option genInjectivity false

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange.ZeroGrind

/-! ## `x % 0 = x`, without `propext` -/

/-- **`x % 0 = x`.** Core's `Nat.mod_zero` depends on `propext`; this proof
unfolds `Nat.mod` and `Nat.modCore` by their (axiom-free) equation lemmas: for
`x = k + 1`, `0 ≤ k + 1` selects the `modCore` branch, and `¬ 0 < 0` selects
its `else x` branch. -/
theorem mod_zero' : ∀ x : Nat, x % 0 = x
  | 0 => Nat.zero_mod 0
  | k + 1 => by
    show Nat.mod (k + 1) 0 = k + 1
    rw [Nat.mod.eq_def]
    show (if 0 ≤ k + 1 then Nat.modCore (k + 1) 0 else k + 1) = k + 1
    rw [if_pos (Nat.zero_le (k + 1)), Nat.modCore.eq_def]
    exact dif_neg (Nat.lt_irrefl 0)

/-! ## Additive lemmas from the semiring fields -/

section Semiring
variable {R : Type} [Semiring R]

/-- `0 + a = a`, from `add_comm` and `add_zero`. -/
theorem zero_add (a : R) : 0 + a = a :=
  Eq.trans (Semiring.add_comm 0 a) (Semiring.add_zero a)

/-- `a + (b + c) = b + (a + c)`. -/
theorem add_left_comm (a b c : R) : a + (b + c) = b + (a + c) :=
  Eq.trans (Eq.symm (Semiring.add_assoc a b c))
    (Eq.trans (congrArg (fun t => t + c) (Semiring.add_comm a b))
      (Semiring.add_assoc b a c))

/-- **Numerals add.** `OfNat.ofNat (m + n) = OfNat.ofNat m + OfNat.ofNat n`,
by induction on `n` with the field `ofNat_succ`. -/
theorem ofNat_add (m : Nat) :
    ∀ n : Nat, (OfNat.ofNat (m + n) : R) = OfNat.ofNat m + OfNat.ofNat n
  | 0 => Eq.symm (Semiring.add_zero (OfNat.ofNat m))
  | n + 1 =>
    Eq.trans (Semiring.ofNat_succ (m + n))
      (Eq.trans (congrArg (fun t => t + 1) (ofNat_add m n))
        (Eq.trans (Semiring.add_assoc (OfNat.ofNat m) (OfNat.ofNat n) 1)
          (congrArg (fun t => OfNat.ofNat m + t) (Eq.symm (Semiring.ofNat_succ n)))))

end Semiring

/-! ## Negation from the ring fields -/

section Ring
variable {R : Type} [Ring R]

/-- **`-a = 0 → a = 0`**, from `neg_add_cancel`. -/
theorem neg_eq_zero {a : R} (h : -a = 0) : a = 0 :=
  Eq.trans (Eq.symm (zero_add a))
    (Eq.trans (congrArg (fun t => t + a) (Eq.symm h)) (Ring.neg_add_cancel a))

end Ring

/-! ## The `IsCharP` test -/

/-- **A numeral that vanishes in characteristic 0 is 0.** Read through the
single field `IsCharP.ofNat_ext_iff` and `mod_zero'`. -/
theorem ofNat_eq_zero_of_charZero {R : Type} [Semiring R] [IsCharP R 0] {k : Nat}
    (h : (OfNat.ofNat k : R) = 0) : k = 0 :=
  Eq.trans (Eq.symm (mod_zero' k))
    (Eq.trans (Iff.mp (IsCharP.ofNat_ext_iff (α := R) 0) h) (mod_zero' 0))

/-- **In characteristic 0, an integer that becomes 0 was already 0.** Same
statement as `SimulationExchange.int_eq_zero_of_cast`. Nonnegative `x = k`:
the cast is the numeral `k` (field `intCast_ofNat`). Negative `x = -(k+1)`: the
cast is `-(k+1)` (fields `intCast_neg`, `intCast_ofNat`), so `k + 1 = 0`. -/
theorem int_eq_zero_of_cast {R : Type} [CommRing R] [IsCharP R 0] (x : Int)
    (h : (Int.cast x : R) = 0) : x = 0 :=
  match x, h with
  | Int.ofNat k, h =>
    congrArg Int.ofNat
      (ofNat_eq_zero_of_charZero (Eq.trans (Eq.symm (Ring.intCast_ofNat k)) h))
  | Int.negSucc k, h =>
    have e : (Int.cast (Int.negSucc k) : R) = -(OfNat.ofNat (k + 1) : R) :=
      Eq.trans (Ring.intCast_neg (OfNat.ofNat (k + 1) : Int))
        (congrArg Neg.neg (Ring.intCast_ofNat (k + 1)))
    Nat.noConfusion
      (ofNat_eq_zero_of_charZero (neg_eq_zero (Eq.trans (Eq.symm e) h)) : k + 1 = 0)

end SimulationExchange.ZeroGrind
