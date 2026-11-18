import SimulationExchange.ZeroRing

/-
  The instructure's own arithmetic as a kernel-checked model (condition E1):
    K_I = ℤ[x₁, x₂] / (x₁² − d₁, x₂² − d₂),
  elements  a + b·x₁ + c·x₂ + e·x₁x₂.
  We prove it is a commutative ring of characteristic 0 in which x₁·x₁ = d₁
  and x₂·x₂ = d₂, so every hypothesis of the exchange theorems is satisfiable.

  Zero-axiom status (see AGENTS.md): every declaration is proved without
  axioms and without `simp`/`omega`/`decide`/`by_cases`/`grind`.
  * `genInjectivity false`: Lean's generated `Inst.mk.injEq` is an equation of
    propositions and needs `propext`; it is not generated. `Inst.mk.inj` is
    restated by hand with its original statement.
  * The ring laws: additive ones component by component with ZeroInt's laws;
    multiplicative ones by the verified normalizer `ZeroRing` over Int, one
    check per component (expression trees in `ModelIdentities`, where `ieMul`
    mirrors the `Mul` instance below).
  * The `simp` attributes formerly on `add_def` … `zsmul_def` are removed here;
    modules that still use `simp` on them declare `attribute [local simp]`
    until they are rewritten.
-/

set_option genInjectivity false

open Lean.Grind

namespace SimulationExchange

@[ext] structure Inst (d₁ d₂ : Int) where
  a : Int
  b : Int
  c : Int
  e : Int

/-- Constructor injectivity, restated by hand (the generated version is
    suppressed by `genInjectivity false`; this proof uses only projections). -/
theorem Inst.mk.inj {d₁ d₂ a b c e a_1 b_1 c_1 e_1 : Int} :
    (Inst.mk a b c e : Inst d₁ d₂) = Inst.mk a_1 b_1 c_1 e_1 →
      a = a_1 ∧ b = b_1 ∧ c = c_1 ∧ e = e_1 :=
  fun h => ⟨congrArg Inst.a h, congrArg Inst.b h, congrArg Inst.c h, congrArg Inst.e h⟩

namespace Inst
variable {d₁ d₂ : Int}

instance : Add (Inst d₁ d₂) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.e + y.e⟩⟩
instance : Neg (Inst d₁ d₂) := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.e⟩⟩
instance : Sub (Inst d₁ d₂) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.e - y.e⟩⟩
/-- The instructure's rewrite rule `x₁² = d₁`, `x₂² = d₂`, applied to products. -/
instance : Mul (Inst d₁ d₂) := ⟨fun x y =>
  ⟨x.a * y.a + d₁ * x.b * y.b + d₂ * x.c * y.c + d₁ * d₂ * x.e * y.e,
   x.a * y.b + x.b * y.a + d₂ * (x.c * y.e + x.e * y.c),
   x.a * y.c + x.c * y.a + d₁ * (x.b * y.e + x.e * y.b),
   x.a * y.e + x.e * y.a + x.b * y.c + x.c * y.b⟩⟩
instance : NatCast (Inst d₁ d₂) := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : IntCast (Inst d₁ d₂) := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance (n : Nat) : OfNat (Inst d₁ d₂) n := ⟨⟨n, 0, 0, 0⟩⟩
instance : SMul Nat (Inst d₁ d₂) := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.e⟩⟩
instance : SMul Int (Inst d₁ d₂) := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.e⟩⟩

def npow (x : Inst d₁ d₂) : Nat → Inst d₁ d₂
  | 0 => ⟨1, 0, 0, 0⟩
  | n + 1 => npow x n * x
instance : HPow (Inst d₁ d₂) Nat (Inst d₁ d₂) := ⟨npow⟩

theorem add_def (x y : Inst d₁ d₂) : x + y = ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.e + y.e⟩ := rfl
theorem neg_def (x : Inst d₁ d₂) : -x = ⟨-x.a, -x.b, -x.c, -x.e⟩ := rfl
theorem sub_def (x y : Inst d₁ d₂) : x - y = ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.e - y.e⟩ := rfl
theorem mul_def (x y : Inst d₁ d₂) : x * y =
  ⟨x.a * y.a + d₁ * x.b * y.b + d₂ * x.c * y.c + d₁ * d₂ * x.e * y.e,
   x.a * y.b + x.b * y.a + d₂ * (x.c * y.e + x.e * y.c),
   x.a * y.c + x.c * y.a + d₁ * (x.b * y.e + x.e * y.b),
   x.a * y.e + x.e * y.a + x.b * y.c + x.c * y.b⟩ := rfl
theorem ofNat_def (n : Nat) : (OfNat.ofNat n : Inst d₁ d₂) = ⟨n, 0, 0, 0⟩ := rfl
theorem natCast_def (n : Nat) : ((n : Nat) : Inst d₁ d₂) = ⟨n, 0, 0, 0⟩ := rfl
theorem intCast_def (n : Int) : ((n : Int) : Inst d₁ d₂) = ⟨n, 0, 0, 0⟩ := rfl
theorem nsmul_def (n : Nat) (x : Inst d₁ d₂) : n • x = ⟨n * x.a, n * x.b, n * x.c, n * x.e⟩ := rfl
theorem zsmul_def (n : Int) (x : Inst d₁ d₂) : n • x = ⟨n * x.a, n * x.b, n * x.c, n * x.e⟩ := rfl

end Inst

/-! ## Expression trees for the ring laws of `Inst`

An element of `Inst` is represented by four expression trees, one per
component. `ieMul` mirrors the `Mul` instance term for term (same
association), so `ZeroRing.eval` of a component unfolds to exactly the
corresponding component of the product. Atoms: `x.a x.b x.c x.e` = 0–3,
`y.*` = 4–7, `z.*` = 8–11, `d₁` = 12, `d₂` = 13, a natural-number cast `n` = 14. -/

namespace ModelIdentities
open SimulationExchange.ZeroRing (RExpr)

abbrev IE : Type := RExpr × RExpr × RExpr × RExpr

def D₁ : RExpr := RExpr.var 12
def D₂ : RExpr := RExpr.var 13

def X : IE := (RExpr.var 0, RExpr.var 1, RExpr.var 2, RExpr.var 3)
def Y : IE := (RExpr.var 4, RExpr.var 5, RExpr.var 6, RExpr.var 7)
def Z : IE := (RExpr.var 8, RExpr.var 9, RExpr.var 10, RExpr.var 11)
def ZERO : IE := (RExpr.const 0, RExpr.const 0, RExpr.const 0, RExpr.const 0)
def ONE : IE := (RExpr.const 1, RExpr.const 0, RExpr.const 0, RExpr.const 0)
def NCAST : IE := (RExpr.var 14, RExpr.const 0, RExpr.const 0, RExpr.const 0)
def X1 : IE := (RExpr.const 0, RExpr.const 1, RExpr.const 0, RExpr.const 0)
def X2 : IE := (RExpr.const 0, RExpr.const 0, RExpr.const 1, RExpr.const 0)
def D1CAST : IE := (D₁, RExpr.const 0, RExpr.const 0, RExpr.const 0)
def D2CAST : IE := (D₂, RExpr.const 0, RExpr.const 0, RExpr.const 0)

def ieAdd (x y : IE) : IE :=
  (RExpr.add x.1 y.1, RExpr.add x.2.1 y.2.1, RExpr.add x.2.2.1 y.2.2.1,
   RExpr.add x.2.2.2 y.2.2.2)

def ieMul (x y : IE) : IE :=
  (RExpr.add (RExpr.add (RExpr.add (RExpr.mul x.1 y.1)
      (RExpr.mul (RExpr.mul D₁ x.2.1) y.2.1))
      (RExpr.mul (RExpr.mul D₂ x.2.2.1) y.2.2.1))
      (RExpr.mul (RExpr.mul (RExpr.mul D₁ D₂) x.2.2.2) y.2.2.2),
   RExpr.add (RExpr.add (RExpr.mul x.1 y.2.1) (RExpr.mul x.2.1 y.1))
      (RExpr.mul D₂ (RExpr.add (RExpr.mul x.2.2.1 y.2.2.2) (RExpr.mul x.2.2.2 y.2.2.1))),
   RExpr.add (RExpr.add (RExpr.mul x.1 y.2.2.1) (RExpr.mul x.2.2.1 y.1))
      (RExpr.mul D₁ (RExpr.add (RExpr.mul x.2.1 y.2.2.2) (RExpr.mul x.2.2.2 y.2.1))),
   RExpr.add (RExpr.add (RExpr.add (RExpr.mul x.1 y.2.2.2) (RExpr.mul x.2.2.2 y.1))
      (RExpr.mul x.2.1 y.2.2.1)) (RExpr.mul x.2.2.1 y.2.1))

/-- Component `j` (0–3) of an `IE`. -/
def comp (x : IE) : Nat → RExpr
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

end ModelIdentities

namespace Inst
variable {d₁ d₂ : Int}

open SimulationExchange.ZeroRing (eq_of_check atoms intCommRing)
open ModelIdentities

/-- The atom list for three elements and the parameters (and a cast `n`). -/
abbrev env3 (x y z : Inst d₁ d₂) (n : Int) : Nat → Int :=
  @atoms Int intCommRing
    [x.a, x.b, x.c, x.e, y.a, y.b, y.c, y.e, z.a, z.b, z.c, z.e, d₁, d₂, n]

instance : CommRing (Inst d₁ d₂) where
  add_zero := fun x => Inst.ext (Int.add_zero x.a) (Int.add_zero x.b)
    (Int.add_zero x.c) (Int.add_zero x.e)
  add_comm := fun x y => Inst.ext (SimulationExchange.ZeroInt.add_comm x.a y.a)
    (SimulationExchange.ZeroInt.add_comm x.b y.b) (SimulationExchange.ZeroInt.add_comm x.c y.c)
    (SimulationExchange.ZeroInt.add_comm x.e y.e)
  add_assoc := fun x y z => Inst.ext (SimulationExchange.ZeroInt.add_assoc x.a y.a z.a)
    (SimulationExchange.ZeroInt.add_assoc x.b y.b z.b)
    (SimulationExchange.ZeroInt.add_assoc x.c y.c z.c)
    (SimulationExchange.ZeroInt.add_assoc x.e y.e z.e)
  mul_assoc := fun x y z => Inst.ext
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieMul X Y) Z) 0) (comp (ieMul X (ieMul Y Z)) 0) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieMul X Y) Z) 1) (comp (ieMul X (ieMul Y Z)) 1) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieMul X Y) Z) 2) (comp (ieMul X (ieMul Y Z)) 2) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieMul X Y) Z) 3) (comp (ieMul X (ieMul Y Z)) 3) rfl)
  mul_one := fun x => Inst.ext
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ONE) 0) (comp X 0) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ONE) 1) (comp X 1) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ONE) 2) (comp X 2) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ONE) 3) (comp X 3) rfl)
  one_mul := fun x => Inst.ext
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ONE X) 0) (comp X 0) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ONE X) 1) (comp X 1) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ONE X) 2) (comp X 2) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ONE X) 3) (comp X 3) rfl)
  left_distrib := fun x y z => Inst.ext
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul X (ieAdd Y Z)) 0) (comp (ieAdd (ieMul X Y) (ieMul X Z)) 0) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul X (ieAdd Y Z)) 1) (comp (ieAdd (ieMul X Y) (ieMul X Z)) 1) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul X (ieAdd Y Z)) 2) (comp (ieAdd (ieMul X Y) (ieMul X Z)) 2) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul X (ieAdd Y Z)) 3) (comp (ieAdd (ieMul X Y) (ieMul X Z)) 3) rfl)
  right_distrib := fun x y z => Inst.ext
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieAdd X Y) Z) 0) (comp (ieAdd (ieMul X Z) (ieMul Y Z)) 0) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieAdd X Y) Z) 1) (comp (ieAdd (ieMul X Z) (ieMul Y Z)) 1) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieAdd X Y) Z) 2) (comp (ieAdd (ieMul X Z) (ieMul Y Z)) 2) rfl)
    (@eq_of_check Int intCommRing (env3 x y z 0)
      (comp (ieMul (ieAdd X Y) Z) 3) (comp (ieAdd (ieMul X Z) (ieMul Y Z)) 3) rfl)
  zero_mul := fun x => Inst.ext
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ZERO X) 0) (comp ZERO 0) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ZERO X) 1) (comp ZERO 1) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ZERO X) 2) (comp ZERO 2) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul ZERO X) 3) (comp ZERO 3) rfl)
  mul_zero := fun x => Inst.ext
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ZERO) 0) (comp ZERO 0) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ZERO) 1) (comp ZERO 1) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ZERO) 2) (comp ZERO 2) rfl)
    (@eq_of_check Int intCommRing (env3 x x x 0) (comp (ieMul X ZERO) 3) (comp ZERO 3) rfl)
  pow_zero := by intro x; rfl
  pow_succ := by intro x n; rfl
  ofNat_succ := fun _ => rfl
  ofNat_eq_natCast := by intro n; rfl
  nsmul_eq_natCast_mul := fun n x => Inst.ext
    (@eq_of_check Int intCommRing (env3 x x x n)
      (ZeroRing.RExpr.mul (ZeroRing.RExpr.var 14) (comp X 0)) (comp (ieMul NCAST X) 0) rfl)
    (@eq_of_check Int intCommRing (env3 x x x n)
      (ZeroRing.RExpr.mul (ZeroRing.RExpr.var 14) (comp X 1)) (comp (ieMul NCAST X) 1) rfl)
    (@eq_of_check Int intCommRing (env3 x x x n)
      (ZeroRing.RExpr.mul (ZeroRing.RExpr.var 14) (comp X 2)) (comp (ieMul NCAST X) 2) rfl)
    (@eq_of_check Int intCommRing (env3 x x x n)
      (ZeroRing.RExpr.mul (ZeroRing.RExpr.var 14) (comp X 3)) (comp (ieMul NCAST X) 3) rfl)
  neg_add_cancel := fun x => Inst.ext
    (Eq.trans (SimulationExchange.ZeroInt.add_comm (-x.a) x.a)
      (SimulationExchange.ZeroInt.add_neg_cancel x.a))
    (Eq.trans (SimulationExchange.ZeroInt.add_comm (-x.b) x.b)
      (SimulationExchange.ZeroInt.add_neg_cancel x.b))
    (Eq.trans (SimulationExchange.ZeroInt.add_comm (-x.c) x.c)
      (SimulationExchange.ZeroInt.add_neg_cancel x.c))
    (Eq.trans (SimulationExchange.ZeroInt.add_comm (-x.e) x.e)
      (SimulationExchange.ZeroInt.add_neg_cancel x.e))
  sub_eq_add_neg := fun _ _ => rfl
  neg_zsmul := fun i x => Inst.ext (SimulationExchange.ZeroInt.neg_mul i x.a)
    (SimulationExchange.ZeroInt.neg_mul i x.b) (SimulationExchange.ZeroInt.neg_mul i x.c)
    (SimulationExchange.ZeroInt.neg_mul i x.e)
  zsmul_natCast_eq_nsmul := fun _ _ => rfl
  intCast_ofNat := by intro n; rfl
  intCast_neg := fun _ => rfl
  mul_comm := fun x y => Inst.ext
    (@eq_of_check Int intCommRing (env3 x y y 0) (comp (ieMul X Y) 0) (comp (ieMul Y X) 0) rfl)
    (@eq_of_check Int intCommRing (env3 x y y 0) (comp (ieMul X Y) 1) (comp (ieMul Y X) 1) rfl)
    (@eq_of_check Int intCommRing (env3 x y y 0) (comp (ieMul X Y) 2) (comp (ieMul Y X) 2) rfl)
    (@eq_of_check Int intCommRing (env3 x y y 0) (comp (ieMul X Y) 3) (comp (ieMul Y X) 3) rfl)

/-- Characteristic 0. `IsCharP`'s single field is stated with `% 0`
    (`OfNat.ofNat x = OfNat.ofNat y ↔ x % 0 = y % 0`), so the instance is read
    through `ZeroGrind.mod_zero'` (`x % 0 = x`), the accepted `% 0` reading of
    AGENTS.md. -/
instance : IsCharP (Inst d₁ d₂) 0 where
  ofNat_ext_iff := fun {x y} =>
    ⟨fun h => congrArg (fun n => n % 0)
        (Int.ofNat.inj (congrArg Inst.a h : Int.ofNat x = Int.ofNat y)),
     fun h => by
       have hxy : x = y :=
         Eq.trans (Eq.symm (SimulationExchange.ZeroGrind.mod_zero' x))
           (Eq.trans h (SimulationExchange.ZeroGrind.mod_zero' y))
       subst hxy
       rfl⟩

/-- The first generator `x₁`. -/
def x₁ : Inst d₁ d₂ := ⟨0, 1, 0, 0⟩
/-- The second generator `x₂`. -/
def x₂ : Inst d₁ d₂ := ⟨0, 0, 1, 0⟩

/-- The instruction, one line per generator: `x₁ · x₁ = d₁`. -/
theorem x₁_sq : (x₁ : Inst d₁ d₂) * x₁ = ((d₁ : Int) : Inst d₁ d₂) := Inst.ext
  (@eq_of_check Int intCommRing (env3 (x₁ : Inst d₁ d₂) x₁ x₁ 0) (comp (ieMul X1 X1) 0) (comp D1CAST 0) rfl)
  (@eq_of_check Int intCommRing (env3 (x₁ : Inst d₁ d₂) x₁ x₁ 0) (comp (ieMul X1 X1) 1) (comp D1CAST 1) rfl)
  (@eq_of_check Int intCommRing (env3 (x₁ : Inst d₁ d₂) x₁ x₁ 0) (comp (ieMul X1 X1) 2) (comp D1CAST 2) rfl)
  (@eq_of_check Int intCommRing (env3 (x₁ : Inst d₁ d₂) x₁ x₁ 0) (comp (ieMul X1 X1) 3) (comp D1CAST 3) rfl)
/-- `x₂ · x₂ = d₂`. -/
theorem x₂_sq : (x₂ : Inst d₁ d₂) * x₂ = ((d₂ : Int) : Inst d₁ d₂) := Inst.ext
  (@eq_of_check Int intCommRing (env3 (x₂ : Inst d₁ d₂) x₂ x₂ 0) (comp (ieMul X2 X2) 0) (comp D2CAST 0) rfl)
  (@eq_of_check Int intCommRing (env3 (x₂ : Inst d₁ d₂) x₂ x₂ 0) (comp (ieMul X2 X2) 1) (comp D2CAST 1) rfl)
  (@eq_of_check Int intCommRing (env3 (x₂ : Inst d₁ d₂) x₂ x₂ 0) (comp (ieMul X2 X2) 2) (comp D2CAST 2) rfl)
  (@eq_of_check Int intCommRing (env3 (x₂ : Inst d₁ d₂) x₂ x₂ 0) (comp (ieMul X2 X2) 3) (comp D2CAST 3) rfl)

end Inst
end SimulationExchange
