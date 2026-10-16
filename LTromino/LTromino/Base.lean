/-!
# LTromino.Base — the 2×2 base unit: D₄, the chiral diagonals, and V₄

Pure core Lean 4, no Mathlib.

A cell of the 2×2 is a pair of bits. A quadrant of a bisected board is also a
pair of bits. Cells and quadrants are the same type, `Cell`, so the central
bridge one scale up *is* the base tromino (`centralBridge_eq`), definitionally.

Every quantified statement in this file ranges over bits and is decided by
the kernel, so every declaration here is expected to depend on no axioms.
That is checked in `LTromino/AxiomCheck.lean`.

Coordinates: `false = 0`, `true = 1`; first bit is x, second is y.
Corners in counter-clockwise order: (0,0) → (1,0) → (1,1) → (0,1).
-/

namespace LTromino

/-! ## §1 Cells, equality and the L-tromino -/

/-- A cell of the 2×2 (equally: a quadrant of a bisected board). -/
abbrev Cell := Bool × Bool

/-- Bool-valued cell equality, written out so no derived instance is used. -/
def cellEq (c d : Cell) : Bool := (c.1 == d.1) && (c.2 == d.2)

/-- Bool-valued list membership (replaces Prop-level `List.Mem`). -/
def memC (l : List Cell) (c : Cell) : Bool := l.any (cellEq c)

/-- The four nodes of the 2×2. -/
def allCells : List Cell := [(false, false), (false, true), (true, false), (true, true)]

/-- Removing corner `m` leaves the residual L-tromino. -/
def trominoFromMissing (m : Cell) : List Cell := allCells.filter (fun c => !cellEq c m)

/-- Membership in the tromino missing `m`. -/
def inTromino (m c : Cell) : Bool := !cellEq c m

/-- Theorem 1a (non-vacuity): removing (0,0) leaves exactly (0,1), (1,0), (1,1). -/
theorem base_witness_non_vacuous :
    trominoFromMissing (false, false) = [(false, true), (true, false), (true, true)] := rfl

/-- Theorem 1b: every one of the four removals leaves exactly three nodes. -/
theorem base_2x2_minus_1_is_tromino :
    ∀ x y : Bool, (trominoFromMissing (x, y)).length = 3 := by decide

/-- The list and the predicate describe the same three cells. -/
theorem memC_tromino_iff :
    ∀ mx my cx cy : Bool,
      memC (trominoFromMissing (mx, my)) (cx, cy) = inTromino (mx, my) (cx, cy) := by decide

/-! ## §2 The bisection bridge is the base case one scale up -/

/-- Quadrants of a bisected board are pairs of bits, the same type as cells. -/
abbrev Quadrant := Cell

/-- The central bridge covers one cell in every quadrant except `q_missing`. -/
def centralBridge (q_missing : Quadrant) : List Quadrant := trominoFromMissing q_missing

/-- **Self-similarity.** The bridge at scale n+1 is the base tromino, with
    quadrants in place of cells. Nothing is proved here because nothing needs to
    be: the two are the same definition. -/
theorem centralBridge_eq : centralBridge = trominoFromMissing := rfl

/-- Theorem 2: the central bridge always spans exactly three quadrants. -/
theorem central_bridge_is_tromino :
    ∀ x y : Bool, (centralBridge (x, y)).length = 3 := by decide

/-- Deficiencies landing on quadrant `q`: the original hole, plus the bridge. -/
def deficiencyCount (q_missing q : Quadrant) : Nat :=
  (if cellEq q q_missing then 1 else 0) + (if memC (centralBridge q_missing) q then 1 else 0)

/-- Theorem 3: after the bridge, every quadrant has exactly one deficiency. -/
theorem bisection_preserves_single_deficiency :
    ∀ mx my qx qy : Bool, deficiencyCount (mx, my) (qx, qy) = 1 := by decide

/-! ## §3 The symmetries of the 2×2 (D₄)

Every symmetry of the square is: optionally swap the two coordinates, then
XOR-flip each coordinate. Three bits, eight symmetries. The flips alone
(`s = false`) are the Klein four switches of `Switching.lean`. -/

-- No generated `mk.inj`/`mk.injEq`: Lean's `mk.injEq` depends on `propext`, and CI audits
-- every declaration against an empty allowlist (docs/notes/LTromino_Axiom_Audit_Scope_and_CI_Enforcement.md).
set_option genInjectivity false in
/-- A symmetry: `s` swaps the coordinates, then `a` flips x and `b` flips y. -/
structure Sym where
  s : Bool
  a : Bool
  b : Bool
  deriving DecidableEq

/-- How a symmetry moves a cell. -/
def act (g : Sym) (c : Cell) : Cell :=
  ((if g.s then c.2 else c.1) ^^ g.a, (if g.s then c.1 else c.2) ^^ g.b)

/-- Composition: `mul g h` is "do h, then g". -/
def mul (g h : Sym) : Sym :=
  ⟨g.s ^^ h.s, g.a ^^ (if g.s then h.b else h.a), g.b ^^ (if g.s then h.a else h.b)⟩

def idS      : Sym := ⟨false, false, false⟩
/-- Quarter turn counter-clockwise: (x, y) ↦ (1−y, x). -/
def rot90    : Sym := ⟨true,  true,  false⟩
/-- Half turn, both bits flipped: the Phantom Middle π. -/
def rot180   : Sym := ⟨false, true,  true⟩
def rot270   : Sym := ⟨true,  false, true⟩
/-- Mirror across the vertical bisector (flip x): σ. -/
def mirrorX  : Sym := ⟨false, true,  false⟩
/-- Mirror across the horizontal bisector (flip y): τ. -/
def mirrorY  : Sym := ⟨false, false, true⟩
/-- Reflection across the main diagonal D1 (the chiral swap (x, y) ↦ (y, x)). -/
def reflD1   : Sym := ⟨true,  false, false⟩
/-- Reflection across the anti-diagonal D2: (x, y) ↦ (1−y, 1−x). -/
def reflD2   : Sym := ⟨true,  true,  true⟩

theorem rot90_values :
    act rot90 (false, false) = (true, false) ∧ act rot90 (true, false) = (true, true) ∧
    act rot90 (true, true) = (false, true) ∧ act rot90 (false, true) = (false, false) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Composition really is composition of the moves. -/
theorem act_mul : ∀ gs ga gb hs ha hb x y : Bool,
    act (mul ⟨gs, ga, gb⟩ ⟨hs, ha, hb⟩) (x, y) = act ⟨gs, ga, gb⟩ (act ⟨hs, ha, hb⟩ (x, y)) := by
  decide

/-- Every symmetry undoes: applying `inv g` after `g` returns every cell. -/
def inv (g : Sym) : Sym :=
  ⟨g.s, if g.s then g.b else g.a, if g.s then g.a else g.b⟩

theorem act_inv : ∀ s a b x y : Bool, act (inv ⟨s, a, b⟩) (act ⟨s, a, b⟩ (x, y)) = (x, y) := by
  decide

/-- Faithfulness: two symmetries that move all four cells alike are equal, so
    the three bits name eight genuinely different motions of the square. -/
theorem act_faithful : ∀ gs ga gb hs ha hb : Bool,
    (act ⟨gs, ga, gb⟩ (false, false) = act ⟨hs, ha, hb⟩ (false, false) ∧
     act ⟨gs, ga, gb⟩ (true, false) = act ⟨hs, ha, hb⟩ (true, false) ∧
     act ⟨gs, ga, gb⟩ (false, true) = act ⟨hs, ha, hb⟩ (false, true)) →
    (gs = hs ∧ ga = ha ∧ gb = hb) := by
  decide

/-- The quarter turn has order four and generates all rotations. -/
theorem rot90_order_four :
    mul rot90 rot90 = rot180 ∧ mul rot90 rot180 = rot270 ∧ mul rot90 rot270 = idS := by
  decide

/-! ## §4 Orientation, read from the cycle of corners

Discrete-first: handedness is not a real determinant here. It is whether a
symmetry carries the counter-clockwise successor of each corner to the
counter-clockwise successor of its image (preserving), or to the clockwise one
(reversing). The integer determinant is then shown to agree with it. -/

/-- Counter-clockwise successor of a corner. -/
def ccw (c : Cell) : Cell := act rot90 c
/-- Clockwise successor of a corner. -/
def cw (c : Cell) : Cell := act rot270 c

/-- The orientation bit: `true` exactly when the symmetry reverses handedness. -/
def sign (g : Sym) : Bool := g.s ^^ g.a ^^ g.b

/-- Orientation-preserving means: commutes with the corner cycle. -/
theorem sign_false_iff_preserves : ∀ s a b : Bool,
    sign ⟨s, a, b⟩ = false ↔
      (∀ x y : Bool, act ⟨s, a, b⟩ (ccw (x, y)) = ccw (act ⟨s, a, b⟩ (x, y))) := by
  decide

/-- Orientation-reversing means: turns the corner cycle around. -/
theorem sign_true_iff_reverses : ∀ s a b : Bool,
    sign ⟨s, a, b⟩ = true ↔
      (∀ x y : Bool, act ⟨s, a, b⟩ (ccw (x, y)) = cw (act ⟨s, a, b⟩ (x, y))) := by
  decide

/-- The orientation bit composes by XOR (chiral sign law on the square). -/
theorem sign_mul : ∀ gs ga gb hs ha hb : Bool,
    sign (mul ⟨gs, ga, gb⟩ ⟨hs, ha, hb⟩) = (sign ⟨gs, ga, gb⟩ ^^ sign ⟨hs, ha, hb⟩) := by
  decide

/-- Rotations keep handedness; every reflection reverses it. -/
theorem sign_table :
    sign idS = false ∧ sign rot90 = false ∧ sign rot180 = false ∧ sign rot270 = false ∧
    sign mirrorX = true ∧ sign mirrorY = true ∧ sign reflD1 = true ∧ sign reflD2 = true := by
  decide

/-! ### The integer determinant agrees with the corner cycle

Centre the cell coordinates at the phantom middle: bit `b` becomes `±1`.
Each symmetry is then an integer 2×2 matrix acting on (±1, ±1). -/

/-- A bit, centred: 0 ↦ −1, 1 ↦ +1. -/
def cen (b : Bool) : Int := if b then 1 else -1
/-- −1 when the flip bit is set, otherwise +1. -/
def eps (b : Bool) : Int := if b then -1 else 1

/-- The integer matrix (m₀₀, m₀₁, m₁₀, m₁₁) of a symmetry on centred coordinates. -/
def mat (g : Sym) : Int × Int × Int × Int :=
  if g.s then (0, eps g.a, eps g.b, 0) else (eps g.a, 0, 0, eps g.b)

def det (g : Sym) : Int :=
  let m := mat g
  m.1 * m.2.2.2 - m.2.1 * m.2.2.1

/-- The matrix really is the move: on centred coordinates, `act g` is `mat g`. -/
theorem act_is_linear : ∀ s a b x y : Bool,
    cen (act ⟨s, a, b⟩ (x, y)).1 = (mat ⟨s, a, b⟩).1 * cen x + (mat ⟨s, a, b⟩).2.1 * cen y ∧
    cen (act ⟨s, a, b⟩ (x, y)).2 = (mat ⟨s, a, b⟩).2.2.1 * cen x + (mat ⟨s, a, b⟩).2.2.2 * cen y := by
  decide

/-- **Determinant = corner-cycle orientation.** det is −1 exactly for the
    reversing symmetries. Flipping one axis gives −1; flipping both gives +1. -/
theorem det_eq_sign : ∀ s a b : Bool,
    det ⟨s, a, b⟩ = (if sign ⟨s, a, b⟩ then -1 else 1) := by
  decide

/-! ## §5 The chiral diagonals -/

/-- A cell lies on the main diagonal D1 = {(0,0), (1,1)}; otherwise on D2. -/
def onD1 (c : Cell) : Bool := c.1 == c.2

/-- Whether a symmetry exchanges the two diagonals: the XOR of its flip bits. -/
def swapsDiag (g : Sym) : Bool := g.a ^^ g.b

/-- **Diagonal law.** Every symmetry of the square either keeps both diagonals or
    exchanges them, and which one it does is `a XOR b`. -/
theorem onD1_act : ∀ s a b x y : Bool,
    onD1 (act ⟨s, a, b⟩ (x, y)) = (onD1 (x, y) ^^ swapsDiag ⟨s, a, b⟩) := by
  decide

theorem swapsDiag_table :
    swapsDiag idS = false ∧ swapsDiag rot180 = false ∧
    swapsDiag reflD1 = false ∧ swapsDiag reflD2 = false ∧
    swapsDiag rot90 = true ∧ swapsDiag rot270 = true ∧
    swapsDiag mirrorX = true ∧ swapsDiag mirrorY = true := by
  decide

/-- Diagonal exchange also composes by XOR. -/
theorem swapsDiag_mul : ∀ gs ga gb hs ha hb : Bool,
    swapsDiag (mul ⟨gs, ga, gb⟩ ⟨hs, ha, hb⟩) =
      (swapsDiag ⟨gs, ga, gb⟩ ^^ swapsDiag ⟨hs, ha, hb⟩) := by
  decide

/-! ### The chiral swap on cells (§15b of `Boundary.lean`, one scale down)

With bit values 0/1, the shared coordinate is x + y and the depth coordinate is
x − y. The reflection across D1 fixes the first and negates the second. -/

def bitI (b : Bool) : Int := if b then 1 else 0
def cellD1 (c : Cell) : Int := bitI c.1 + bitI c.2
def cellD2 (c : Cell) : Int := bitI c.1 - bitI c.2

theorem chiral_swap_on_cells : ∀ x y : Bool,
    cellD1 (act reflD1 (x, y)) = cellD1 (x, y) ∧ cellD2 (act reflD1 (x, y)) = -cellD2 (x, y) := by
  decide

/-- The D1 reflection fixes exactly the D1 cells; the D2 reflection fixes exactly the D2 cells. -/
theorem refl_fixes_own_diagonal : ∀ x y : Bool,
    (act reflD1 (x, y) = (x, y) ↔ onD1 (x, y) = true) ∧
    (act reflD2 (x, y) = (x, y) ↔ onD1 (x, y) = false) := by
  decide

/-! ## §6 The Klein four layer and the Phantom Middle

The pair (orientation bit, diagonal-exchange bit) is a map from D₄ onto the
Klein four group (pairs of bits under XOR). It respects composition, reaches
all four values, and its kernel is {id, π}. The Phantom Middle π is the centre
of D₄: the one non-trivial symmetry that commutes with every other. -/

/-- The two chiral bits of a symmetry. -/
def chiralBits (g : Sym) : Cell := (sign g, swapsDiag g)

theorem chiralBits_mul : ∀ gs ga gb hs ha hb : Bool,
    chiralBits (mul ⟨gs, ga, gb⟩ ⟨hs, ha, hb⟩) =
      (( chiralBits ⟨gs, ga, gb⟩).1 ^^ (chiralBits ⟨hs, ha, hb⟩).1,
       ( chiralBits ⟨gs, ga, gb⟩).2 ^^ (chiralBits ⟨hs, ha, hb⟩).2) := by
  decide

/-- Onto: each of the four values is reached. -/
theorem chiralBits_onto :
    chiralBits idS = (false, false) ∧ chiralBits rot90 = (false, true) ∧
    chiralBits reflD1 = (true, false) ∧ chiralBits mirrorX = (true, true) := by
  decide

/-- Kernel: both chiral bits vanish exactly for the identity and π. -/
theorem chiralBits_kernel : ∀ s a b : Bool,
    chiralBits ⟨s, a, b⟩ = (false, false) ↔
      ((s, a, b) = (false, false, false) ∨ (s, a, b) = (false, true, true)) := by
  decide

/-- **π is the centre.** A symmetry commutes with all eight exactly when it is
    the identity or the Phantom Middle. -/
theorem centre_is_phantom_middle : ∀ s a b : Bool,
    (∀ hs ha hb : Bool, mul ⟨s, a, b⟩ ⟨hs, ha, hb⟩ = mul ⟨hs, ha, hb⟩ ⟨s, a, b⟩) ↔
      ((s, a, b) = (false, false, false) ∨ (s, a, b) = (false, true, true)) := by
  decide

/-- The flips (no swap) are the Klein four switches: closed, composing by XOR. -/
theorem flips_are_klein_four : ∀ a b a' b' : Bool,
    mul ⟨false, a, b⟩ ⟨false, a', b'⟩ = ⟨false, a ^^ a', b ^^ b'⟩ := by
  decide

/-- Among the switches, π is the only non-trivial one that keeps handedness
    (cf. §4.3 of *Two Walkers and a Tick*). -/
theorem phantom_middle_unique_preserving_switch : ∀ a b : Bool,
    (sign ⟨false, a, b⟩ = false ∧ (a, b) ≠ (false, false)) ↔ (a, b) = (true, true) := by
  decide

/-! ## §7 The L-orientation invariant -/

/-- The elbow of the L missing `m`: the corner opposite `m`, i.e. `π m`. -/
def elbow (m : Cell) : Cell := act rot180 m

/-- Edge-adjacent cells differ in exactly one bit. -/
def adj (c d : Cell) : Bool := (c.1 != d.1) != (c.2 != d.2)

/-- The elbow belongs to the L. -/
theorem elbow_in_tromino : ∀ x y : Bool, inTromino (x, y) (elbow (x, y)) = true := by
  decide

/-- **The missing corner and the elbow share a diagonal.** -/
theorem elbow_same_diagonal : ∀ x y : Bool, onD1 (elbow (x, y)) = onD1 (x, y) := by
  decide

/-- **The two arms are exactly the other diagonal.** -/
theorem arms_are_other_diagonal : ∀ mx my cx cy : Bool,
    (inTromino (mx, my) (cx, cy) && !cellEq (cx, cy) (elbow (mx, my))) =
      (onD1 (cx, cy) != onD1 (mx, my)) := by
  decide

/-- **The elbow is the one cell of the L touching both others.** -/
theorem elbow_unique_hub : ∀ mx my cx cy : Bool,
    inTromino (mx, my) (cx, cy) = true →
      ((∀ dx dy : Bool, inTromino (mx, my) (dx, dy) = true → cellEq (dx, dy) (cx, cy) = false →
          adj (cx, cy) (dx, dy) = true) ↔ (cx, cy) = elbow (mx, my)) := by
  decide

/-- Symmetries carry L's to L's: moving the hole moves the shape. -/
theorem tromino_equivariant : ∀ s a b mx my cx cy : Bool,
    inTromino (act ⟨s, a, b⟩ (mx, my)) (act ⟨s, a, b⟩ (cx, cy)) = inTromino (mx, my) (cx, cy) := by
  decide

/-- The reflection through the missing corner's own diagonal. -/
def mirrorThrough (m : Cell) : Sym := if onD1 m then reflD1 else reflD2

/-- **Each L has exactly one mirror axis, its own diagonal.** A symmetry maps the
    L missing `m` onto itself exactly when it is the identity or the reflection
    across the diagonal through `m` and the elbow. -/
theorem tromino_stabilizer : ∀ s a b mx my : Bool,
    ((∀ cx cy : Bool,
        inTromino (mx, my) (act ⟨s, a, b⟩ (cx, cy)) = inTromino (mx, my) (cx, cy)) ↔
      ((s, a, b) = (false, false, false) ∨
        (⟨s, a, b⟩ : Sym) = mirrorThrough (mx, my))) := by
  intro s a b mx my
  cases s <;> cases a <;> cases b <;> cases mx <;> cases my <;> decide

/-- **Chirality lives in the placement, not the shape.** For any two L
    orientations, exactly one rotation and exactly one reflection carry the
    first to the second. -/
theorem one_rotation_one_reflection : ∀ mx my nx ny : Bool,
    ([idS, rot90, rot180, rot270].filter
        (fun g => cellEq (act g (mx, my)) (nx, ny))).length = 1 ∧
    ([mirrorX, mirrorY, reflD1, reflD2].filter
        (fun g => cellEq (act g (mx, my)) (nx, ny))).length = 1 := by
  decide

/-! ## §8 Necessity: each hypothesis is load-bearing -/

/-- Deficiency count with the bridge's missing corner `bm` chosen freely. -/
def deficiencyWith (bm q_missing q : Quadrant) : Nat :=
  (if cellEq q q_missing then 1 else 0) + (if memC (trominoFromMissing bm) q then 1 else 0)

/-- **The bridge's orientation is forced.** Every quadrant ends with exactly one
    deficiency if and only if the bridge's missing corner is the deficient
    quadrant. -/
theorem bridge_orientation_forced : ∀ bx by_ mx my : Bool,
    (∀ qx qy : Bool, deficiencyWith (bx, by_) (mx, my) (qx, qy) = 1) ↔ (bx, by_) = (mx, my) := by
  decide

/-- Counterexample along the diagonal: orient the bridge with its gap at π(q)
    instead of q. Quadrant q gets two deficiencies and π(q) gets none. -/
theorem misoriented_along_diagonal :
    deficiencyWith (true, true) (false, false) (false, false) = 2 ∧
    deficiencyWith (true, true) (false, false) (true, true) = 0 := by
  decide

/-- Counterexample off the diagonal: gap at (1,0) for a hole in (0,0). -/
theorem misoriented_off_diagonal :
    deficiencyWith (true, false) (false, false) (false, false) = 2 ∧
    deficiencyWith (true, false) (false, false) (true, false) = 0 := by
  decide

/-- Deficiencies with two holes, in quadrants `q₁` and `q₂`. -/
def deficiencyTwo (bm q₁ q₂ q : Quadrant) : Nat :=
  (if cellEq q q₁ then 1 else 0) + (if cellEq q q₂ then 1 else 0) +
    (if memC (trominoFromMissing bm) q then 1 else 0)

/-- **Two holes break conservation.** With holes in two different quadrants, no
    orientation of the bridge leaves every quadrant with exactly one deficiency. -/
theorem two_holes_break_conservation : ∀ ax ay bx by_ cx cy : Bool,
    cellEq (ax, ay) (bx, by_) = false →
      allCells.any (fun q => deficiencyTwo (cx, cy) (ax, ay) (bx, by_) q != 1) = true := by
  decide

/-- Two cells removed from a 2×2 leave two cells, not an L. The leftover pair is
    edge-connected exactly when the removed pair was (a domino leaves a domino);
    removing a diagonal pair leaves the other diagonal, two cells with no edge. -/
theorem two_removed_no_tromino : ∀ ax ay bx by_ : Bool,
    cellEq (ax, ay) (bx, by_) = false →
      (allCells.filter (fun c => !cellEq c (ax, ay) && !cellEq c (bx, by_))).length = 2 := by
  decide

theorem diagonal_pair_disconnected :
    adj (false, false) (true, true) = false ∧ adj (true, false) (false, true) = false := by
  decide

end LTromino

