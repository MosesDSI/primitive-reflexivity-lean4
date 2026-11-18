import SimulationExchange.ZeroGrind

/-!
# ZeroRing — a verified commutative-ring normalizer (proof by reflection)

Polynomial identities in any `Lean.Grind.CommRing R` are proved here without
`simp`, `ring`, `grind` or `decide`:

1. Write both sides as `RExpr` trees, by hand (no reification tactic).
2. `normalize` turns a tree into a sorted list of (integer coefficient,
   monomial) pairs with zero coefficients removed. It is defined by structural
   recursion only, so the kernel evaluates it, and comparisons use `Nat.beq` /
   `Nat.ble` through `cond`.
3. `normalize_eval` (soundness, proved once from ZeroGrind's ring lemmas):
   `eval env e = evalPoly env (normalize e)`.
4. `eq_of_normalize_eq`: if `normalize e₁ = normalize e₂` (checked by `rfl`,
   i.e. by kernel evaluation of two closed lists), then
   `eval env e₁ = eval env e₂` in every commutative ring and environment.

Only soundness is proved. If two equal polynomials normalized differently, a
proof would fail to check; it could not prove a false statement.

**Usage.** Write each expression tree as a named top-level `def` (not an inline
`let` inside the proof term: the elaborator then expands the `let`s and the
check can take minutes instead of seconds), supply the atoms with `atoms [...]`
(not core's `List.getD`, which reaches `propext`), and close with the Boolean
check:

    def eL : RExpr := ...
    def eR : RExpr := ...
    theorem foo ... : lhs = rhs := eq_of_check (atoms [x₀, x₁, ...]) (e₁ := eL) (e₂ := eR) rfl

For identities over `Int`, pass the zero-axiom structure explicitly:
`@eq_of_check Int intCommRing (@atoms Int intCommRing [...]) eL eR rfl`.

Hygiene: no `simp`, `omega`, `decide`, `by_cases`, `grind`; no Nat subtraction;
no well-founded recursion. Target: zero axioms for every declaration.
-/

set_option genInjectivity false

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange.ZeroRing

open SimulationExchange.ZeroGrind

/-! ## Syntax -/

/-- Ring expressions over integer constants and numbered atoms. -/
inductive RExpr : Type where
  | const : Int → RExpr
  | var : Nat → RExpr
  | add : RExpr → RExpr → RExpr
  | sub : RExpr → RExpr → RExpr
  | mul : RExpr → RExpr → RExpr
  | neg : RExpr → RExpr

/-- A monomial: the multiset of its atoms, as a nondecreasing list. -/
abbrev Mon : Type := List Nat
/-- A polynomial: (coefficient, monomial) pairs, sorted by monomial. -/
abbrev Poly : Type := List (Int × Mon)

/-! ## Decisions, by structural recursion -/

/-- `c = 0`, decided by the constructors of `Int`. -/
def isZero : Int → Bool
  | Int.ofNat 0 => true
  | Int.ofNat (_ + 1) => false
  | Int.negSucc _ => false

theorem isZero_true : ∀ {c : Int}, isZero c = true → c = 0
  | Int.ofNat 0, _ => rfl
  | Int.ofNat (_ + 1), h => Bool.noConfusion h
  | Int.negSucc _, h => Bool.noConfusion h

/-- Order of two atoms. -/
def cmpNat (a b : Nat) : Ordering :=
  cond (Nat.beq a b) Ordering.eq (cond (Nat.ble a b) Ordering.lt Ordering.gt)

theorem cmpNat_eq {a b : Nat} (h : cmpNat a b = Ordering.eq) : a = b := by
  have h' : cond (Nat.beq a b) Ordering.eq (cond (Nat.ble a b) Ordering.lt Ordering.gt)
      = Ordering.eq := h
  cases hb : Nat.beq a b with
  | true => exact Nat.eq_of_beq_eq_true hb
  | false =>
    rw [hb] at h'
    cases hl : Nat.ble a b with
    | true => rw [hl] at h'; exact Ordering.noConfusion h'
    | false => rw [hl] at h'; exact Ordering.noConfusion h'

/-- Lexicographic refinement: the first ordering unless it is `eq`. -/
def thenCmp : Ordering → Ordering → Ordering
  | Ordering.eq, o => o
  | Ordering.lt, _ => Ordering.lt
  | Ordering.gt, _ => Ordering.gt

theorem thenCmp_eq : ∀ {a b : Ordering}, thenCmp a b = Ordering.eq →
    a = Ordering.eq ∧ b = Ordering.eq
  | Ordering.eq, _, h => ⟨rfl, h⟩
  | Ordering.lt, _, h => Ordering.noConfusion h
  | Ordering.gt, _, h => Ordering.noConfusion h

/-- Lexicographic order of monomials. -/
def cmpMon : Mon → Mon → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | i :: m, j :: m' => thenCmp (cmpNat i j) (cmpMon m m')

theorem cmpMon_eq : ∀ {m m' : Mon}, cmpMon m m' = Ordering.eq → m = m'
  | [], [], _ => rfl
  | [], _ :: _, h => Ordering.noConfusion h
  | _ :: _, [], h => Ordering.noConfusion h
  | i :: m, j :: m', h =>
    match thenCmp_eq (h : thenCmp (cmpNat i j) (cmpMon m m') = Ordering.eq) with
    | ⟨h₁, h₂⟩ => by
      rw [cmpNat_eq h₁, cmpMon_eq h₂]

/-! ## Monomials and polynomials -/

/-- Insert an atom into a sorted monomial. -/
def insertVar (i : Nat) : Mon → Mon
  | [] => [i]
  | j :: m => cond (Nat.ble i j) (i :: j :: m) (j :: insertVar i m)

/-- Product of monomials: insert the atoms of the first into the second. -/
def mulMon : Mon → Mon → Mon
  | [], m₂ => m₂
  | i :: m₁, m₂ => insertVar i (mulMon m₁ m₂)

/-- The step of `addTerm'` at a head term `(c', m')`, given the comparison
`o = cmpMon m m'` and the recursive result `rest` (for `o = gt`). -/
def addTermCase (c : Int) (m : Mon) (c' : Int) (m' : Mon) (p rest : Poly) :
    Ordering → Poly
  | Ordering.lt => (c, m) :: (c', m') :: p
  | Ordering.eq => cond (isZero (c + c')) p ((c + c', m') :: p)
  | Ordering.gt => (c', m') :: rest

/-- Add a term to a sorted polynomial (coefficient assumed nonzero). -/
def addTerm' (c : Int) (m : Mon) : Poly → Poly
  | [] => [(c, m)]
  | (c', m') :: p => addTermCase c m c' m' p (addTerm' c m p) (cmpMon m m')

/-- Add a term, dropping it if its coefficient is zero. -/
def addTerm (c : Int) (m : Mon) (p : Poly) : Poly :=
  cond (isZero c) p (addTerm' c m p)

def padd : Poly → Poly → Poly
  | [], q => q
  | (c, m) :: p, q => addTerm c m (padd p q)

/-- Multiply a polynomial by one term. -/
def mulTerm (c : Int) (m : Mon) : Poly → Poly
  | [] => []
  | (c', m') :: q => addTerm (c * c') (mulMon m m') (mulTerm c m q)

def pmul : Poly → Poly → Poly
  | [], _ => []
  | (c, m) :: p, q => padd (mulTerm c m q) (pmul p q)

/-- **The normalizer.** -/
def normalize : RExpr → Poly
  | RExpr.const c => addTerm c [] []
  | RExpr.var i => [(1, [i])]
  | RExpr.add a b => padd (normalize a) (normalize b)
  | RExpr.sub a b => padd (normalize a) (mulTerm (-1) [] (normalize b))
  | RExpr.mul a b => pmul (normalize a) (normalize b)
  | RExpr.neg a => mulTerm (-1) [] (normalize a)

/-! ## Semantics -/

section Eval
variable {R : Type} [CommRing R]

def evalMon (env : Nat → R) : Mon → R
  | [] => 1
  | i :: m => env i * evalMon env m

def evalPoly (env : Nat → R) : Poly → R
  | [] => 0
  | (c, m) :: p => Int.cast c * evalMon env m + evalPoly env p

/-- **Evaluation of an expression** in a commutative ring. -/
def eval (env : Nat → R) : RExpr → R
  | RExpr.const c => Int.cast c
  | RExpr.var i => env i
  | RExpr.add a b => eval env a + eval env b
  | RExpr.sub a b => eval env a - eval env b
  | RExpr.mul a b => eval env a * eval env b
  | RExpr.neg a => -(eval env a)

/-! ## Soundness -/

theorem insertVar_eval (env : Nat → R) (i : Nat) :
    ∀ m : Mon, evalMon env (insertVar i m) = env i * evalMon env m
  | [] => rfl
  | j :: m => by
    show evalMon env (cond (Nat.ble i j) (i :: j :: m) (j :: insertVar i m))
      = env i * (env j * evalMon env m)
    cases Nat.ble i j with
    | true => rfl
    | false =>
      show env j * evalMon env (insertVar i m) = env i * (env j * evalMon env m)
      rw [insertVar_eval env i m]
      exact mul_left_comm (env j) (env i) (evalMon env m)

theorem mulMon_eval (env : Nat → R) :
    ∀ m₁ m₂ : Mon, evalMon env (mulMon m₁ m₂) = evalMon env m₁ * evalMon env m₂
  | [], m₂ => Eq.symm (Semiring.one_mul (evalMon env m₂))
  | i :: m₁, m₂ => by
    show evalMon env (insertVar i (mulMon m₁ m₂)) = env i * evalMon env m₁ * evalMon env m₂
    rw [insertVar_eval, mulMon_eval env m₁ m₂]
    exact Eq.symm (Semiring.mul_assoc (env i) (evalMon env m₁) (evalMon env m₂))

theorem addTerm'_eval (env : Nat → R) (c : Int) (m : Mon) :
    ∀ p : Poly, evalPoly env (addTerm' c m p) = Int.cast c * evalMon env m + evalPoly env p
  | [] => rfl
  | (c', m') :: p => by
    show evalPoly env (addTermCase c m c' m' p (addTerm' c m p) (cmpMon m m'))
      = Int.cast c * evalMon env m + (Int.cast c' * evalMon env m' + evalPoly env p)
    cases ho : cmpMon m m' with
    | lt => rfl
    | eq =>
      have hm : m = m' := cmpMon_eq ho
      subst hm
      show evalPoly env (cond (isZero (c + c')) p ((c + c', m) :: p))
        = Int.cast c * evalMon env m + (Int.cast c' * evalMon env m + evalPoly env p)
      have hsum : Int.cast c * evalMon env m + (Int.cast c' * evalMon env m + evalPoly env p)
          = Int.cast (c + c') * evalMon env m + evalPoly env p := by
        rw [← Semiring.add_assoc, ← Semiring.right_distrib, ← intCast_add]
      rw [hsum]
      cases hz : isZero (c + c') with
      | false => rfl
      | true =>
        show evalPoly env p = Int.cast (c + c') * evalMon env m + evalPoly env p
        rw [isZero_true hz, intCast_zero, Semiring.zero_mul, zero_add]
    | gt =>
      show Int.cast c' * evalMon env m' + evalPoly env (addTerm' c m p)
        = Int.cast c * evalMon env m + (Int.cast c' * evalMon env m' + evalPoly env p)
      rw [addTerm'_eval env c m p]
      exact add_left_comm _ _ _

theorem addTerm_eval (env : Nat → R) (c : Int) (m : Mon) (p : Poly) :
    evalPoly env (addTerm c m p) = Int.cast c * evalMon env m + evalPoly env p := by
  show evalPoly env (cond (isZero c) p (addTerm' c m p)) = _
  cases hz : isZero c with
  | false => exact addTerm'_eval env c m p
  | true =>
    show evalPoly env p = Int.cast c * evalMon env m + evalPoly env p
    rw [isZero_true hz, intCast_zero, Semiring.zero_mul, zero_add]

theorem padd_eval (env : Nat → R) :
    ∀ p q : Poly, evalPoly env (padd p q) = evalPoly env p + evalPoly env q
  | [], q => Eq.symm (zero_add (evalPoly env q))
  | (c, m) :: p, q => by
    show evalPoly env (addTerm c m (padd p q))
      = Int.cast c * evalMon env m + evalPoly env p + evalPoly env q
    rw [addTerm_eval, padd_eval env p q]
    exact Eq.symm (Semiring.add_assoc _ _ _)

theorem mulTerm_eval (env : Nat → R) (c : Int) (m : Mon) :
    ∀ q : Poly, evalPoly env (mulTerm c m q) = Int.cast c * evalMon env m * evalPoly env q
  | [] => Eq.symm (Semiring.mul_zero _)
  | (c', m') :: q => by
    show evalPoly env (addTerm (c * c') (mulMon m m') (mulTerm c m q))
      = Int.cast c * evalMon env m * (Int.cast c' * evalMon env m' + evalPoly env q)
    rw [addTerm_eval, mulTerm_eval env c m q, intCast_mul, mulMon_eval, Semiring.left_distrib,
      mul_mul_mul_comm (Int.cast c : R) (Int.cast c') (evalMon env m) (evalMon env m')]

theorem pmul_eval (env : Nat → R) :
    ∀ p q : Poly, evalPoly env (pmul p q) = evalPoly env p * evalPoly env q
  | [], q => Eq.symm (Semiring.zero_mul (evalPoly env q))
  | (c, m) :: p, q => by
    show evalPoly env (padd (mulTerm c m q) (pmul p q))
      = (Int.cast c * evalMon env m + evalPoly env p) * evalPoly env q
    rw [padd_eval, mulTerm_eval, pmul_eval env p q, Semiring.right_distrib]

/-- Multiplying by the constant term `-1` negates. -/
theorem negOne_eval (env : Nat → R) (q : Poly) :
    evalPoly env (mulTerm (-1) [] q) = -(evalPoly env q) := by
  rw [mulTerm_eval]
  show (Int.cast (-1) : R) * 1 * evalPoly env q = -(evalPoly env q)
  rw [Ring.intCast_neg, intCast_one, Semiring.mul_one, neg_mul, Semiring.one_mul]

/-- **Soundness of the normalizer.** -/
theorem normalize_eval (env : Nat → R) :
    ∀ e : RExpr, eval env e = evalPoly env (normalize e)
  | RExpr.const c => by
    show (Int.cast c : R) = evalPoly env (addTerm c [] [])
    rw [addTerm_eval]
    exact Eq.symm (Eq.trans (Semiring.add_zero _) (Semiring.mul_one _))
  | RExpr.var i => by
    show env i = Int.cast 1 * (env i * 1) + 0
    rw [intCast_one, Semiring.one_mul, Semiring.mul_one, Semiring.add_zero]
  | RExpr.add a b => by
    show eval env a + eval env b = evalPoly env (padd (normalize a) (normalize b))
    rw [padd_eval, normalize_eval env a, normalize_eval env b]
  | RExpr.sub a b => by
    show eval env a - eval env b
      = evalPoly env (padd (normalize a) (mulTerm (-1) [] (normalize b)))
    rw [padd_eval, negOne_eval, normalize_eval env a, normalize_eval env b,
      Ring.sub_eq_add_neg]
  | RExpr.mul a b => by
    show eval env a * eval env b = evalPoly env (pmul (normalize a) (normalize b))
    rw [pmul_eval, normalize_eval env a, normalize_eval env b]
  | RExpr.neg a => by
    show -(eval env a) = evalPoly env (mulTerm (-1) [] (normalize a))
    rw [negOne_eval, normalize_eval env a]

/-- **Proof by reflection.** Equal normal forms give equal values, in every
commutative ring and every environment. -/
theorem eq_of_normalize_eq (env : Nat → R) {e₁ e₂ : RExpr}
    (h : normalize e₁ = normalize e₂) : eval env e₁ = eval env e₂ :=
  Eq.trans (normalize_eval env e₁)
    (Eq.trans (congrArg (evalPoly env) h) (Eq.symm (normalize_eval env e₂)))

end Eval

/-! ## A Boolean check, so `rfl` must evaluate

Checking `normalize e₁ = normalize e₂` by `rfl` lets the elaborator compare
the two unevaluated sides piece by piece, which can blow up. Asking instead
for `polyBEq (normalize e₁) (normalize e₂) = true` forces it to evaluate the
left side down to the constructor `true`. -/

def andB : Bool → Bool → Bool
  | true, b => b
  | false, _ => false

theorem andB_true : ∀ {a b : Bool}, andB a b = true → a = true ∧ b = true
  | true, _, h => ⟨rfl, h⟩
  | false, _, h => Bool.noConfusion h

def intBEq : Int → Int → Bool
  | Int.ofNat a, Int.ofNat b => Nat.beq a b
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc _, Int.ofNat _ => false
  | Int.negSucc a, Int.negSucc b => Nat.beq a b

theorem intBEq_eq : ∀ {a b : Int}, intBEq a b = true → a = b
  | Int.ofNat _, Int.ofNat _, h => congrArg Int.ofNat (Nat.eq_of_beq_eq_true h)
  | Int.ofNat _, Int.negSucc _, h => Bool.noConfusion h
  | Int.negSucc _, Int.ofNat _, h => Bool.noConfusion h
  | Int.negSucc _, Int.negSucc _, h => congrArg Int.negSucc (Nat.eq_of_beq_eq_true h)

def monBEq : Mon → Mon → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | i :: m, j :: m' => andB (Nat.beq i j) (monBEq m m')

theorem monBEq_eq : ∀ {m m' : Mon}, monBEq m m' = true → m = m'
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | _ :: _, _ :: _, h =>
    match andB_true h with
    | ⟨h₁, h₂⟩ => by rw [Nat.eq_of_beq_eq_true h₁, monBEq_eq h₂]

def polyBEq : Poly → Poly → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | (c, m) :: p, (c', m') :: q => andB (intBEq c c') (andB (monBEq m m') (polyBEq p q))

theorem polyBEq_eq : ∀ {p q : Poly}, polyBEq p q = true → p = q
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | (_, _) :: _, (_, _) :: _, h =>
    match andB_true h with
    | ⟨h₁, h₂⟩ =>
      match andB_true h₂ with
      | ⟨h₃, h₄⟩ => by rw [intBEq_eq h₁, monBEq_eq h₃, polyBEq_eq h₄]

/-- Variable values from a list, by structural recursion. (Core's `List.getD`
is avoided: its lookup reaches `propext` through `Nat.bitwise`.) -/
def atoms {R : Type} [CommRing R] : List R → Nat → R
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => atoms xs n

/-- **Proof by reflection, checked as a Boolean.** Use with `rfl` for `h`. -/
theorem eq_of_check {R : Type} [CommRing R] (env : Nat → R) {e₁ e₂ : RExpr}
    (h : polyBEq (normalize e₁) (normalize e₂) = true) : eval env e₁ = eval env e₂ :=
  eq_of_normalize_eq env (polyBEq_eq h)

/-! ## A zero-axiom commutative-ring structure on `Int`

Core's `Lean.Grind.CommRing Int` instance proves its fields with lemmas that
carry axioms. `intCommRing` is assembled from ZeroInt's proved laws instead.
It is a `def`, not an instance: pass it explicitly (`(R := Int)
(inst := intCommRing)`) so that core's instance is never silently replaced.
Its data fields are Int's ordinary operations, so `eval` agrees with `+`, `*`,
`-` on `Int` by definition. -/

/-- Power by Peano recursion, so that `pow_succ` holds by definition. -/
def intPow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => intPow x n * x

@[instance_reducible]
def intCommRing : CommRing Int where
  nsmul := ⟨fun n x => (n : Int) * x⟩
  npow := ⟨intPow⟩
  zsmul := ⟨fun i x => i * x⟩
  add_zero := Int.add_zero
  add_comm := SimulationExchange.ZeroInt.add_comm
  add_assoc := SimulationExchange.ZeroInt.add_assoc
  mul_assoc := SimulationExchange.ZeroInt.mul_assoc
  mul_one := SimulationExchange.ZeroInt.mul_one
  one_mul := Int.one_mul
  left_distrib := SimulationExchange.ZeroInt.mul_add
  right_distrib := SimulationExchange.ZeroInt.add_mul
  zero_mul := SimulationExchange.ZeroInt.zero_mul
  mul_zero := Int.mul_zero
  pow_zero := fun _ => rfl
  pow_succ := fun _ _ => rfl
  neg_add_cancel := fun a =>
    Eq.trans (SimulationExchange.ZeroInt.add_comm (-a) a) (SimulationExchange.ZeroInt.add_neg_cancel a)
  sub_eq_add_neg := fun _ _ => rfl
  neg_zsmul := fun i a => SimulationExchange.ZeroInt.neg_mul i a
  mul_comm := SimulationExchange.ZeroInt.mul_comm

end SimulationExchange.ZeroRing
