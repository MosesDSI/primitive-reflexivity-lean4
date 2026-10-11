/-
  The instructure's own arithmetic as a kernel-checked model (condition E1):
    K_I = ℤ[x₁, x₂] / (x₁² − d₁, x₂² − d₂),
  elements  a + b·x₁ + c·x₂ + e·x₁x₂.
  We prove it is a commutative ring of characteristic 0 in which x₁·x₁ = d₁
  and x₂·x₂ = d₂, so every hypothesis of the exchange theorems is satisfiable.
-/
open Lean.Grind

namespace SimulationExchange

@[ext] structure Inst (d₁ d₂ : Int) where
  a : Int
  b : Int
  c : Int
  e : Int

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

@[simp] theorem add_def (x y : Inst d₁ d₂) : x + y = ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.e + y.e⟩ := rfl
@[simp] theorem neg_def (x : Inst d₁ d₂) : -x = ⟨-x.a, -x.b, -x.c, -x.e⟩ := rfl
@[simp] theorem sub_def (x y : Inst d₁ d₂) : x - y = ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.e - y.e⟩ := rfl
@[simp] theorem mul_def (x y : Inst d₁ d₂) : x * y =
  ⟨x.a * y.a + d₁ * x.b * y.b + d₂ * x.c * y.c + d₁ * d₂ * x.e * y.e,
   x.a * y.b + x.b * y.a + d₂ * (x.c * y.e + x.e * y.c),
   x.a * y.c + x.c * y.a + d₁ * (x.b * y.e + x.e * y.b),
   x.a * y.e + x.e * y.a + x.b * y.c + x.c * y.b⟩ := rfl
@[simp] theorem ofNat_def (n : Nat) : (OfNat.ofNat n : Inst d₁ d₂) = ⟨n, 0, 0, 0⟩ := rfl
@[simp] theorem natCast_def (n : Nat) : ((n : Nat) : Inst d₁ d₂) = ⟨n, 0, 0, 0⟩ := rfl
@[simp] theorem intCast_def (n : Int) : ((n : Int) : Inst d₁ d₂) = ⟨n, 0, 0, 0⟩ := rfl
@[simp] theorem nsmul_def (n : Nat) (x : Inst d₁ d₂) : n • x = ⟨n * x.a, n * x.b, n * x.c, n * x.e⟩ := rfl
@[simp] theorem zsmul_def (n : Int) (x : Inst d₁ d₂) : n • x = ⟨n * x.a, n * x.b, n * x.c, n * x.e⟩ := rfl

instance : CommRing (Inst d₁ d₂) where
  add_zero := by intro x; ext <;> simp
  add_comm := by intro x y; ext <;> simp <;> omega
  add_assoc := by intro x y z; ext <;> simp <;> omega
  mul_assoc := by intro x y z; ext <;> simp <;> grind
  mul_one := by intro x; ext <;> simp
  one_mul := by intro x; ext <;> simp
  left_distrib := by intro x y z; ext <;> simp <;> grind
  right_distrib := by intro x y z; ext <;> simp <;> grind
  zero_mul := by intro x; ext <;> simp
  mul_zero := by intro x; ext <;> simp
  pow_zero := by intro x; rfl
  pow_succ := by intro x n; rfl
  ofNat_succ := by intro n; ext <;> simp
  ofNat_eq_natCast := by intro n; rfl
  nsmul_eq_natCast_mul := by intro n x; ext <;> simp
  neg_add_cancel := by intro x; ext <;> simp <;> omega
  sub_eq_add_neg := by intro x y; ext <;> simp <;> omega
  neg_zsmul := by intro i x; ext <;> simp [Int.neg_mul]
  zsmul_natCast_eq_nsmul := by intro n x; ext <;> simp
  intCast_ofNat := by intro n; rfl
  intCast_neg := by intro i; ext <;> simp
  mul_comm := by intro x y; ext <;> simp <;> grind

instance : IsCharP (Inst d₁ d₂) 0 where
  ofNat_ext_iff := by
    intro x y
    constructor
    · intro h
      have := congrArg Inst.a h
      simp at this
      omega
    · intro h
      simp at h
      simp [h]

/-- The first generator `x₁`. -/
def x₁ : Inst d₁ d₂ := ⟨0, 1, 0, 0⟩
/-- The second generator `x₂`. -/
def x₂ : Inst d₁ d₂ := ⟨0, 0, 1, 0⟩

/-- The instruction, one line per generator: `x₁ · x₁ = d₁`. -/
theorem x₁_sq : (x₁ : Inst d₁ d₂) * x₁ = ((d₁ : Int) : Inst d₁ d₂) := by
  ext <;> simp [x₁]
/-- `x₂ · x₂ = d₂`. -/
theorem x₂_sq : (x₂ : Inst d₁ d₂) * x₂ = ((d₂ : Int) : Inst d₁ d₂) := by
  ext <;> simp [x₂]

end Inst
end SimulationExchange
