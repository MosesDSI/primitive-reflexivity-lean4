import LTromino.Base
import SimulationExchange.Switching

/-!
# LTromino.WalkerBridge — §4.3 of *Two Walkers and a Tick*, kernel-checked

§4.3 says: flipping one walker reflects one axis and reverses handedness
(determinant −1); flipping both reflects both axes, which is the half turn
and keeps handedness (determinant +1).

The walkers live in the instructure model `SimulationExchange.Inst d₁ d₂`
(`a + b·x₁ + c·x₂ + e·x₁x₂`). Walker 1 steps along the generator `x₁`, walker 2
along `x₂`, so the two walker axes are the generator coordinates `(b, c)`. A
flip is `Inst.switch p q` (the world table of §4.1), and exchanging the two
walkers (§15b) swaps the generators.

The bridge is not a relabelling of `Base.mat`. The matrix `d4_to_walker g` is
**read off the walker operations themselves**: run the operation named by
`g` (exchange the walkers if `g.s`, then `switch g.a g.b`) on the two unit
generators and record where they land. Then:

* `switch_represents`, `exchange_switch_represents`: that matrix *is* what the
  operation does to the walker coordinates of every element `x`, for all
  `d₁ d₂`, not just on the probes;
* `walker_matrix_eq_mat`: it equals D₄'s integer matrix on centred cells;
* `walker_matrix_det_eq_d4_det`, `universal_walker_flip_eq_sign`: its
  determinant is D₄'s, and is `−1` exactly for the reversing symmetries.

Everything is core Lean with no axioms; checked in `LTromino/AxiomCheck.lean`.
-/

namespace LTromino

open SimulationExchange

/-! ## Axiom-free integer facts (core's `Int.zero_mul`, `Int.zero_add` use `propext`) -/

theorem int_zero_mul' : ∀ c : Int, 0 * c = 0
  | .ofNat n => congrArg Int.ofNat (Nat.zero_mul n)
  | .negSucc n => (congrArg Int.negOfNat (Nat.zero_mul (n + 1)) : Int.negOfNat (0 * (n + 1)) = _)

theorem int_zero_add' : ∀ c : Int, 0 + c = c
  | .ofNat n => congrArg Int.ofNat (Nat.zero_add n)
  | .negSucc _ => rfl

/-! ## Walker coordinates, the walker exchange, and walker matrices -/

/-- The walker coordinates of an instructure element: its `x₁` and `x₂` coefficients. -/
def gens {d₁ d₂ : Int} (x : Inst d₁ d₂) : Int × Int := (x.b, x.c)

/-- Exchanging the two walkers: the generators trade places (§15b). -/
def exchange {d₁ d₂ : Int} (x : Inst d₁ d₂) : Inst d₂ d₁ := ⟨x.a, x.c, x.b, x.e⟩

/-- The exchange really trades the walker generators. -/
theorem exchange_x₁ {d₁ d₂ : Int} : exchange (Inst.x₁ : Inst d₁ d₂) = Inst.x₂ := rfl
theorem exchange_x₂ {d₁ d₂ : Int} : exchange (Inst.x₂ : Inst d₁ d₂) = Inst.x₁ := rfl

set_option genInjectivity false in
/-- An integer 2×2 matrix on the walker coordinates. -/
structure WalkerMatrix where
  m00 : Int
  m01 : Int
  m10 : Int
  m11 : Int
  deriving DecidableEq

def WalkerMatrix.det (M : WalkerMatrix) : Int := M.m00 * M.m11 - M.m01 * M.m10

def WalkerMatrix.apply (M : WalkerMatrix) (u v : Int) : Int × Int :=
  (M.m00 * u + M.m01 * v, M.m10 * u + M.m11 * v)

/-- The walker operation named by `g`, on the walker coordinates of a probe:
    exchange the walkers if `g.s`, then switch to world `(g.a, g.b)`. -/
def walkerOpGens (g : Sym) (u v : Int) : Int × Int :=
  if g.s then gens (Inst.switch g.a g.b (exchange (⟨0, u, v, 0⟩ : Inst 0 0)))
  else gens (Inst.switch g.a g.b (⟨0, u, v, 0⟩ : Inst 0 0))

/-- **The embedding D₄ → walker matrices**, read off the walker operation:
    the columns are the images of the unit generators `x₁` and `x₂`. -/
def d4_to_walker (g : Sym) : WalkerMatrix :=
  ⟨(walkerOpGens g 1 0).1, (walkerOpGens g 0 1).1,
   (walkerOpGens g 1 0).2, (walkerOpGens g 0 1).2⟩

/-! ## The matrix is the walker operation, on every element -/

theorem d4_to_walker_flip (p q : Bool) :
    d4_to_walker ⟨false, p, q⟩ = ⟨Inst.sgn p, 0, 0, Inst.sgn q⟩ := by
  cases p <;> cases q <;> decide

theorem d4_to_walker_exchange (p q : Bool) :
    d4_to_walker ⟨true, p, q⟩ = ⟨0, Inst.sgn p, Inst.sgn q, 0⟩ := by
  cases p <;> cases q <;> decide

/-- **A switch acts on the walker coordinates by its matrix**, for every
    element of every instructure. -/
theorem switch_represents {d₁ d₂ : Int} (p q : Bool) (x : Inst d₁ d₂) :
    gens (Inst.switch p q x) = (d4_to_walker ⟨false, p, q⟩).apply x.b x.c := by
  rw [d4_to_walker_flip]
  show (Inst.sgn p * x.b, Inst.sgn q * x.c) =
    (Inst.sgn p * x.b + 0 * x.c, 0 * x.b + Inst.sgn q * x.c)
  rw [int_zero_mul', int_zero_mul', Int.add_zero, int_zero_add']

/-- **Exchange-then-switch acts on the walker coordinates by its matrix**,
    for every element of every instructure. -/
theorem exchange_switch_represents {d₁ d₂ : Int} (p q : Bool) (x : Inst d₁ d₂) :
    gens (Inst.switch p q (exchange x)) = (d4_to_walker ⟨true, p, q⟩).apply x.b x.c := by
  rw [d4_to_walker_exchange]
  show (Inst.sgn p * x.c, Inst.sgn q * x.b) =
    (0 * x.b + Inst.sgn p * x.c, Inst.sgn q * x.b + 0 * x.c)
  rw [int_zero_mul', int_zero_mul', Int.add_zero, int_zero_add']

/-! ## The walker matrix is D₄'s matrix, and its determinant is the corner-cycle sign -/

/-- The walker matrix is `Base.mat` on centred cells: the walker axes and the
    cell axes carry the same action of D₄. -/
theorem walker_matrix_eq_mat : ∀ s a b : Bool,
    d4_to_walker ⟨s, a, b⟩ =
      ⟨(mat ⟨s, a, b⟩).1, (mat ⟨s, a, b⟩).2.1, (mat ⟨s, a, b⟩).2.2.1, (mat ⟨s, a, b⟩).2.2.2⟩ := by
  decide

theorem walker_matrix_det_eq_d4_det (g : Sym) : (d4_to_walker g).det = det g := by
  obtain ⟨s, a, b⟩ := g
  cases s <;> cases a <;> cases b <;> rfl

/-- **§4.3, universally.** For every one of the eight walker operations, the
    determinant on the walker axes is `−1` exactly when the operation reverses
    the corner cycle, and `+1` otherwise. -/
theorem universal_walker_flip_eq_sign (g : Sym) :
    (d4_to_walker g).det = (if sign g then -1 else 1) :=
  (walker_matrix_det_eq_d4_det g).trans (det_eq_sign g.s g.a g.b)

/-! ## The sentences of §4.3, one by one -/

/-- Flipping one walker reflects one axis and reverses handedness. -/
theorem one_flip_reflects_one_axis :
    d4_to_walker ⟨false, true, false⟩ = ⟨-1, 0, 0, 1⟩ ∧
    d4_to_walker ⟨false, false, true⟩ = ⟨1, 0, 0, -1⟩ ∧
    (d4_to_walker ⟨false, true, false⟩).det = -1 ∧
    (d4_to_walker ⟨false, false, true⟩).det = -1 := by
  decide

/-- Flipping both walkers reflects both axes, is the 180° rotation of D₄,
    and keeps handedness. -/
theorem both_flips_half_turn :
    d4_to_walker ⟨false, true, true⟩ = ⟨-1, 0, 0, -1⟩ ∧
    (⟨false, true, true⟩ : Sym) = rot180 ∧
    (d4_to_walker ⟨false, true, true⟩).det = 1 := by
  decide

/-- The switch determinant composes by XOR: it is `sgn (p xor q)`, the same
    sign the §4.1 table puts on the `x₁x₂` column. -/
theorem switch_det_eq_sgn_xor : ∀ p q : Bool,
    (d4_to_walker ⟨false, p, q⟩).det = Inst.sgn (p ^^ q) := by
  decide

/-- Among the four switches, π is the only non-trivial one that keeps
    handedness on the walker axes. -/
theorem phantom_middle_unique_on_walkers : ∀ p q : Bool,
    ((d4_to_walker ⟨false, p, q⟩).det = 1 ∧ (p, q) ≠ (false, false)) ↔ (p, q) = (true, true) := by
  decide

/-! ## Non-vacuity and necessity -/

/-- On a concrete walker element of `Inst 2 3` (`3·x₁ − 5·x₂ + 7·x₁x₂ + 4`),
    σ negates the walker-1 coordinate and π negates both. -/
theorem switch_on_sample :
    gens (Inst.switch true false (⟨4, 3, -5, 7⟩ : Inst 2 3)) = (-3, -5) ∧
    gens (Inst.switch true true (⟨4, 3, -5, 7⟩ : Inst 2 3)) = (-3, 5) := by
  decide

/-- **Switches alone reach only half of D₄.** No switch has the walker matrix
    of an axis-exchanging symmetry, so the exchange of §15b is needed to
    realise all eight. -/
theorem swap_needs_exchange : ∀ p q a b : Bool,
    d4_to_walker ⟨false, p, q⟩ ≠ d4_to_walker ⟨true, a, b⟩ := by
  decide

end LTromino
