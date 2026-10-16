import LTromino.Base

/-!
# LTromino.Tiling — the centre geometry and the tiling theorem for every n

Cells of a `2^n × 2^n` board are pairs of naturals `(x, y)` with `x, y < 2^n`.
A tromino is a 2×2 block, named by its lower-left cell, together with the
corner it leaves out (a `Cell` from `Base`). The tiling theorem says: for every
`n` and every hole, the recursive construction covers every board cell other
than the hole exactly once, and nothing else at all.

**Zero axioms.** Every declaration in this file depends on no axioms, not even
`propext`. To get there:

* `covers`, `onBoard`, `hasCorner` and the specification `TilesS` are
  Bool-valued, built from `Nat.ble`, `Nat.beq`, `&&`, `!` and `cond`.
* No `omega`, no `simp`: proofs use only `rw` with equations, `cases`,
  `induction`, `show`, `rfl`, `decide` on closed Bool goals, and core
  lemmas that are themselves axiom-free.
* Core `Nat.sub_add_cancel`, `Nat.add_sub_cancel`, `Nat.beq_refl`,
  `Nat.mul_assoc`, `List.length_append`, `List.length_map`,
  `Bool.and_eq_true` each depend on `propext` in Lean 4.33.1, so local
  inductive versions are proved here.
* Discrete-first: a cell of the `2^(n+1)` board is never located by
  subtracting. It is written as *local cell + quadrant offset*,
  `l + cond b S 0` with `l < S`, and the quadrant bit `b` carries the rest.
-/

namespace LTromino

/-- Bit to number. -/
def b2n (b : Bool) : Nat := cond b 1 0

/-! ## §9 Scaling step (Theorem 4, kernel-checked) -/

/-- Associativity of multiplication, proved by induction from `Nat.mul_succ`
    and `Nat.mul_add`. (Core's `Nat.mul_assoc` depends on `propext` in
    Lean 4.33.1; this one depends on no axioms.) -/
theorem mul_assoc' (a b c : Nat) : a * b * c = a * (b * c) :=
  Nat.rec (motive := fun c => a * b * c = a * (b * c)) rfl
    (fun c ih =>
      have h1 : a * b * (c + 1) = a * b * c + a * b := Nat.mul_succ (a * b) c
      have h2 : a * b * c + a * b = a * (b * c) + a * b := congrArg (· + a * b) ih
      have h3 : a * (b * c) + a * b = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
      have h4 : a * (b * c + b) = a * (b * (c + 1)) := congrArg (a * ·) (Nat.mul_succ b c).symm
      h1.trans (h2.trans (h3.trans h4)))
    c

/-- Theorem 4: four deficient quadrants are four sub-tilings, one bridge, and
    one global hole. -/
theorem scale_bisection_step (k : Nat) : 4 * (3 * k + 1) = 3 * (4 * k + 1) + 1 :=
  calc 4 * (3 * k + 1)
      = 4 * (3 * k) + 4 * 1           := Nat.mul_add 4 (3 * k) 1
    _ = (4 * 3) * k + 4 * 1           := congrArg (· + 4 * 1) (mul_assoc' 4 3 k).symm
    _ = (3 * 4) * k + (3 * 1 + 1)     := rfl
    _ = 3 * (4 * k) + (3 * 1 + 1)     := congrArg (· + (3 * 1 + 1)) (mul_assoc' 3 4 k)
    _ = (3 * (4 * k) + 3 * 1) + 1     := (Nat.add_assoc (3 * (4 * k)) (3 * 1) 1).symm
    _ = 3 * (4 * k + 1) + 1           := congrArg (· + 1) (Nat.mul_add 3 (4 * k) 1).symm

/-! ## §10 An axiom-free toolkit for `Nat.ble` and `Nat.beq` -/

theorem beq_self' : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | a + 1 => beq_self' a

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem ble_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le_of_gt h)

theorem ble_true_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h

/-- `Nat.blt a b` is `Nat.ble (a+1) b`. -/
theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := ble_true_of_le h

theorem blt_false_of_le {a b : Nat} (h : b ≤ a) : Nat.blt a b = false :=
  ble_false_of_lt (Nat.lt_succ_of_le h)

/-- Adding the same amount on the right does not change `≤`. -/
theorem ble_add_right (a b : Nat) : ∀ k, Nat.ble (a + k) (b + k) = Nat.ble a b
  | 0 => rfl
  | k + 1 => ble_add_right a b k

/-- Adding the same amount on the right does not change `=`. -/
theorem beq_add_right (a b : Nat) : ∀ k, Nat.beq (a + k) (b + k) = Nat.beq a b
  | 0 => rfl
  | k + 1 => beq_add_right a b k

/-- `(k + o) − o = k`, by induction (core's version depends on `propext`). -/
theorem add_sub_cancel'' (k : Nat) : ∀ o, (k + o) - o = k
  | 0 => rfl
  | o + 1 => (Nat.succ_sub_succ (k + o) o).trans (add_sub_cancel'' k o)

/-- Splitting a true conjunction (core's `Bool.and_eq_true` depends on `propext`). -/
theorem and_true_split {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x with
  | false => exact absurd h Bool.false_ne_true
  | true => exact ⟨rfl, h⟩

/-! ## §11 Trominoes, covering, and shifting -/

-- No generated `mk.inj`/`mk.injEq`: Lean's `mk.injEq` depends on `propext`, and CI audits
-- every declaration against an empty allowlist (docs/notes/LTromino_Axiom_Audit_Scope_and_CI_Enforcement.md).
set_option genInjectivity false in
/-- A tromino: the 2×2 block with lower-left cell `(x, y)`, minus corner `miss`. -/
structure Tromino where
  x : Nat
  y : Nat
  miss : Cell
  deriving DecidableEq

/-- Whether tromino `t` covers board cell `(cx, cy)`, as a Bool. -/
def covers (t : Tromino) (cx cy : Nat) : Bool :=
  Nat.ble t.x cx && (Nat.ble cx (t.x + 1) && (Nat.ble t.y cy && (Nat.ble cy (t.y + 1) &&
    !(Nat.beq cx (t.x + b2n t.miss.1) && Nat.beq cy (t.y + b2n t.miss.2)))))

/-- How many trominoes of `T` cover `(cx, cy)`. -/
def cov : List Tromino → Nat → Nat → Nat
  | [], _, _ => 0
  | t :: T, cx, cy => cond (covers t cx cy) 1 0 + cov T cx cy

/-- Translate a tromino by `(ox, oy)`. -/
def shift (ox oy : Nat) (t : Tromino) : Tromino := ⟨t.x + ox, t.y + oy, t.miss⟩

theorem cov_append (A B : List Tromino) (cx cy : Nat) :
    cov (A ++ B) cx cy = cov A cx cy + cov B cx cy :=
  List.rec (motive := fun A => cov (A ++ B) cx cy = cov A cx cy + cov B cx cy)
    (Nat.zero_add _).symm
    (fun t _ ih =>
      (congrArg (cond (covers t cx cy) 1 0 + ·) ih).trans
        (Nat.add_assoc _ _ _).symm)
    A

/-- A shifted tromino read at the shifted cell is the original tromino. -/
theorem covers_shift (ox oy : Nat) (t : Tromino) (cx cy : Nat) :
    covers (shift ox oy t) (cx + ox) (cy + oy) = covers t cx cy := by
  show (Nat.ble (t.x + ox) (cx + ox) && (Nat.ble (cx + ox) (t.x + ox + 1) &&
      (Nat.ble (t.y + oy) (cy + oy) && (Nat.ble (cy + oy) (t.y + oy + 1) &&
        !(Nat.beq (cx + ox) (t.x + ox + b2n t.miss.1) &&
          Nat.beq (cy + oy) (t.y + oy + b2n t.miss.2)))))) = covers t cx cy
  rw [Nat.add_right_comm t.x ox 1, Nat.add_right_comm t.y oy 1,
    Nat.add_right_comm t.x ox (b2n t.miss.1), Nat.add_right_comm t.y oy (b2n t.miss.2),
    ble_add_right t.x cx ox, ble_add_right cx (t.x + 1) ox,
    ble_add_right t.y cy oy, ble_add_right cy (t.y + 1) oy,
    beq_add_right cx (t.x + b2n t.miss.1) ox, beq_add_right cy (t.y + b2n t.miss.2) oy]
  rfl

/-- A shifted tromino covers nothing to the left of its shift. -/
theorem covers_shift_lt_x (ox oy : Nat) (t : Tromino) {cx : Nat} (cy : Nat) (h : cx < ox) :
    covers (shift ox oy t) cx cy = false := by
  show (Nat.ble (t.x + ox) cx && _) = false
  rw [ble_false_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_left ox t.x))]
  rfl

theorem and_and_false (x y z : Bool) : (x && (y && (false && z))) = false := by
  cases x <;> cases y <;> rfl

/-- A shifted tromino covers nothing below its shift. -/
theorem covers_shift_lt_y (ox oy : Nat) (t : Tromino) (cx : Nat) {cy : Nat} (h : cy < oy) :
    covers (shift ox oy t) cx cy = false := by
  show (Nat.ble (t.x + ox) cx && (Nat.ble cx (t.x + ox + 1) && (Nat.ble (t.y + oy) cy && _))) = false
  rw [ble_false_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_left oy t.y))]
  exact and_and_false _ _ _

theorem cov_map_shift (ox oy : Nat) (T : List Tromino) (cx cy : Nat) :
    cov (T.map (shift ox oy)) (cx + ox) (cy + oy) = cov T cx cy :=
  List.rec (motive := fun T => cov (T.map (shift ox oy)) (cx + ox) (cy + oy) = cov T cx cy) rfl
    (fun t T ih => by
      show cond (covers (shift ox oy t) (cx + ox) (cy + oy)) 1 0 +
          cov (T.map (shift ox oy)) (cx + ox) (cy + oy) = _
      rw [covers_shift, ih]
      rfl)
    T

theorem cov_map_shift_lt_x (ox oy : Nat) (T : List Tromino) {cx : Nat} (cy : Nat) (h : cx < ox) :
    cov (T.map (shift ox oy)) cx cy = 0 :=
  List.rec (motive := fun T => cov (T.map (shift ox oy)) cx cy = 0) rfl
    (fun t T ih => by
      show cond (covers (shift ox oy t) cx cy) 1 0 + cov (T.map (shift ox oy)) cx cy = 0
      rw [covers_shift_lt_x ox oy t cy h, ih]
      rfl)
    T

theorem cov_map_shift_lt_y (ox oy : Nat) (T : List Tromino) (cx : Nat) {cy : Nat} (h : cy < oy) :
    cov (T.map (shift ox oy)) cx cy = 0 :=
  List.rec (motive := fun T => cov (T.map (shift ox oy)) cx cy = 0) rfl
    (fun t T ih => by
      show cond (covers (shift ox oy t) cx cy) 1 0 + cov (T.map (shift ox oy)) cx cy = 0
      rw [covers_shift_lt_y ox oy t cx h, ih]
      rfl)
    T

/-! ## §12 The board, the specification, and the cell decomposition -/

/-- A cell lies on the `N × N` board. -/
def onBoard (N cx cy : Nat) : Bool := Nat.blt cx N && Nat.blt cy N

/-- The specification at side `S`: every board cell except the hole is covered
    exactly once, and nothing else is covered at all. -/
def TilesS (S : Nat) (T : List Tromino) (hx hy : Nat) : Prop :=
  ∀ cx cy : Nat,
    cov T cx cy = cond (onBoard S cx cy && !(Nat.beq cx hx && Nat.beq cy hy)) 1 0

/-- The specification on the `2^n × 2^n` board. -/
def Tiles (n : Nat) (T : List Tromino) (hx hy : Nat) : Prop := TilesS (2 ^ n) T hx hy

/-- The offset of the half selected by bit `b`, at side `S`. -/
def offS (S : Nat) (b : Bool) : Nat := cond b S 0

theorem onBoard_true {S l l' : Nat} (h : l < S) (h' : l' < S) : onBoard S l l' = true := by
  show (Nat.blt l S && Nat.blt l' S) = true
  rw [blt_true_of_lt h, blt_true_of_lt h']
  rfl

theorem onBoard_far_x {S l : Nat} (l' : Nat) (h : S ≤ l) : onBoard S l l' = false := by
  show (Nat.blt l S && Nat.blt l' S) = false
  rw [blt_false_of_le h]
  rfl

theorem onBoard_far_y {S l : Nat} (l' : Nat) (h : S ≤ l) : onBoard S l' l = false := by
  show (Nat.blt l' S && Nat.blt l S) = false
  rw [blt_false_of_le h]
  exact Bool.and_false _

/-- **Node-first decomposition.** A coordinate on the `2S` board is a local
    coordinate `l < S` plus the offset of its half; the half bit is `S ≤ x`. -/
theorem split_on (S x : Nat) (hx : x < S + S) :
    ∃ b l, l < S ∧ x = l + offS S b ∧ Nat.ble S x = b := by
  cases Nat.lt_or_ge x S with
  | inl h => exact ⟨false, x, h, rfl, ble_false_of_lt h⟩
  | inr h =>
    obtain ⟨l, hl⟩ := Nat.le.dest h
    refine ⟨true, l, ?_, ?_, ble_true_of_le h⟩
    · rw [← hl] at hx; exact Nat.lt_of_add_lt_add_left hx
    · rw [← hl]; exact Nat.add_comm S l

/-- Off the `2S` board, a coordinate is at least `S` beyond either offset. -/
theorem split_far (S x : Nat) (hx : S + S ≤ x) (b : Bool) :
    ∃ l, S ≤ l ∧ x = l + offS S b := by
  cases b with
  | false => exact ⟨x, Nat.le_trans (Nat.le_add_right S S) hx, rfl⟩
  | true =>
    obtain ⟨j, hj⟩ := Nat.le.dest hx
    refine ⟨S + j, Nat.le_add_right S j, ?_⟩
    rw [← hj]
    show S + S + j = S + j + S
    rw [Nat.add_assoc, Nat.add_comm S (S + j)]

/-! ### A sub-tiling read on the big board -/

/-- A shifted sub-tiling covers nothing at cells beyond its own board in x. -/
theorem cov_far_x {S : Nat} {T : List Tromino} {hx hy : Nat} (hT : TilesS S T hx hy)
    (ox oy : Nat) {l : Nat} (hl : S ≤ l) (cy : Nat) :
    cov (T.map (shift ox oy)) (l + ox) cy = 0 := by
  cases Nat.lt_or_ge cy oy with
  | inl h => exact cov_map_shift_lt_y ox oy T _ h
  | inr h =>
    obtain ⟨l', hl'⟩ := Nat.le.dest h
    rw [← hl', Nat.add_comm oy l', cov_map_shift, hT, onBoard_far_x l' hl]
    rfl

/-- A shifted sub-tiling covers nothing at cells beyond its own board in y. -/
theorem cov_far_y {S : Nat} {T : List Tromino} {hx hy : Nat} (hT : TilesS S T hx hy)
    (ox oy : Nat) (cx : Nat) {l : Nat} (hl : S ≤ l) :
    cov (T.map (shift ox oy)) cx (l + oy) = 0 := by
  cases Nat.lt_or_ge cx ox with
  | inl h => exact cov_map_shift_lt_x ox oy T _ h
  | inr h =>
    obtain ⟨l', hl'⟩ := Nat.le.dest h
    rw [← hl', Nat.add_comm ox l', cov_map_shift, hT, onBoard_far_y l' hl]
    rfl

/-- **Quadrant selection.** At an on-board cell written as local cell plus the
    offset of quadrant `(a', b')`, the sub-tiling placed in quadrant `q`
    contributes its own count at the local cell if `q = (a', b')`, and nothing
    otherwise. -/
theorem cov_sub_cell {S : Nat} {T : List Tromino} {hx hy : Nat} (hT : TilesS S T hx hy)
    (q : Cell) (a' b' : Bool) {lx ly : Nat} (hlx : lx < S) (hly : ly < S) :
    cov (T.map (shift (offS S q.1) (offS S q.2))) (lx + offS S a') (ly + offS S b') =
      cond (cellEq q (a', b')) (cov T lx ly) 0 := by
  obtain ⟨q1, q2⟩ := q
  cases q1 <;> cases a' <;> cases q2 <;> cases b'
  -- x halves agree and y halves agree
  all_goals first
    | exact cov_map_shift _ _ T lx ly
    -- x: cell in the lower half, sub-tiling in the upper half
    | exact cov_map_shift_lt_x _ _ T _ (Nat.lt_of_lt_of_le hlx (Nat.le_refl S))
    -- x: cell in the upper half, sub-tiling in the lower half
    | exact cov_far_x hT 0 _ (Nat.le_add_left S lx) _
    -- y: the same two situations
    | exact cov_map_shift_lt_y _ _ T _ (Nat.lt_of_lt_of_le hly (Nat.le_refl S))
    | exact cov_far_y hT _ 0 _ (Nat.le_add_left S ly)

/-! ## §13 The four centre-sharing cells and the phantom intersection -/

/-- The quadrant of a cell, at half-side `S`: bit set when the coordinate is at least `S`. -/
def quadS (S cx cy : Nat) : Cell := (Nat.ble S cx, Nat.ble S cy)

/-- The quadrant of a cell on the `2^(n+1)` board. -/
def quadrantOf (n : Nat) (cx cy : Nat) : Cell := quadS (2 ^ n) cx cy

/-- The central bridge at half-side `S`, leaving out the deficient quadrant. -/
def bridgeS (S : Nat) (qm : Cell) : Tromino := ⟨S - 1, S - 1, qm⟩

/-- The central bridge on the `2^(n+1)` board. -/
def bridge (n : Nat) (qm : Cell) : Tromino := bridgeS (2 ^ n) qm

/-- The centre cell of quadrant `q` on the `2^(n+1)` board:
    `(2^n − 1 + i, 2^n − 1 + j)` for `q = (i, j)`. -/
def centerCell (n : Nat) (q : Cell) : Nat × Nat :=
  (2 ^ n - 1 + b2n q.1, 2 ^ n - 1 + b2n q.2)

/-- A cell has the lattice vertex `(vx, vy)` as one of its four corners. -/
def hasCorner (cx cy vx vy : Nat) : Bool :=
  Nat.ble cx vx && (Nat.ble vx (cx + 1) && (Nat.ble cy vy && Nat.ble vy (cy + 1)))

/-- `2^n` is a successor. -/
theorem two_pow_succ_form (n : Nat) : ∃ p, 2 ^ n = p + 1 := by
  obtain ⟨p, hp⟩ := Nat.le.dest (Nat.two_pow_pos n)
  exact ⟨p, hp.symm.trans (Nat.add_comm 1 p)⟩

theorem two_pow_succ_eq (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n :=
  (Nat.pow_succ (n := 2) (m := n)).trans (Nat.mul_two (2 ^ n))

theorem two_pow_pos' (n : Nat) : 1 ≤ 2 ^ n := Nat.two_pow_pos n

/-! ### One-axis facts at the centre (with `S = p + 1`) -/

/-- Every relevant `≤` and `=` at the centre, as a table over the two bits. -/
theorem ble_center (p : Nat) (u : Bool) : Nat.ble p (p + b2n u) = true := by
  cases u with
  | false => exact ble_true_of_le (Nat.le_refl p)
  | true => exact ble_true_of_le (Nat.le_succ p)

theorem ble_center_up (p : Nat) (u : Bool) : Nat.ble (p + b2n u) (p + 1) = true := by
  cases u with
  | false => exact ble_true_of_le (Nat.le_succ p)
  | true => exact ble_true_of_le (Nat.le_refl (p + 1))

theorem beq_center (p : Nat) (u v : Bool) : Nat.beq (p + b2n u) (p + b2n v) = (u == v) := by
  cases u <;> cases v
  · exact beq_self' p
  · exact beq_false_of_ne (Nat.ne_of_lt (Nat.lt_succ_self p))
  · exact beq_false_of_ne (Nat.ne_of_gt (Nat.lt_succ_self p))
  · exact beq_self' (p + 1)

theorem ble_center_bit (p : Nat) (u : Bool) : Nat.ble (p + 1) (p + b2n u) = u := by
  cases u with
  | false => exact ble_false_of_lt (Nat.lt_succ_self p)
  | true => exact ble_true_of_le (Nat.le_refl (p + 1))

/-- The only coordinates within one step of the centre line `p + 1` are `p`
    and `p + 1`. -/
theorem between_center {p x : Nat} (h1 : p ≤ x) (h2 : x ≤ p + 1) : ∃ u : Bool, x = p + b2n u := by
  cases Nat.eq_or_lt_of_le h1 with
  | inl h => exact ⟨false, h.symm⟩
  | inr h => exact ⟨true, Nat.le_antisymm h2 h⟩

/-- Each centre cell lies in its own quadrant. -/
theorem centerCell_in_quadrant (n : Nat) (i j : Bool) :
    quadrantOf n (centerCell n (i, j)).1 (centerCell n (i, j)).2 = (i, j) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  show (Nat.ble (2 ^ n) (2 ^ n - 1 + b2n i), Nat.ble (2 ^ n) (2 ^ n - 1 + b2n j)) = (i, j)
  rw [hp]
  show (Nat.ble (p + 1) (p + b2n i), Nat.ble (p + 1) (p + b2n j)) = (i, j)
  rw [ble_center_bit, ble_center_bit]

theorem center_lt (p : Nat) (u : Bool) : p + b2n u < (p + 1) + (p + 1) := by
  cases u with
  | false => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self p) (Nat.le_add_right _ _)
  | true => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (p + 1))
              (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le p)) _)

/-- Each centre cell lies on the `2^(n+1)` board. -/
theorem centerCell_on_board (n : Nat) (i j : Bool) :
    (centerCell n (i, j)).1 < 2 ^ (n + 1) ∧ (centerCell n (i, j)).2 < 2 ^ (n + 1) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  show 2 ^ n - 1 + b2n i < 2 ^ (n + 1) ∧ 2 ^ n - 1 + b2n j < 2 ^ (n + 1)
  rw [two_pow_succ_eq, hp]
  exact ⟨center_lt p i, center_lt p j⟩

/-- **The phantom intersection.** A board cell touches the vertex `(2^n, 2^n)`,
    where the two bisectors cross, exactly when it is one of the four centre
    cells. The vertex itself is a corner shared by four cells, never a cell. -/
theorem touches_middle_iff (n cx cy : Nat) :
    hasCorner cx cy (2 ^ n) (2 ^ n) = true ↔ ∃ i j : Bool, (cx, cy) = centerCell n (i, j) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  show (Nat.ble cx (2 ^ n) && (Nat.ble (2 ^ n) (cx + 1) &&
      (Nat.ble cy (2 ^ n) && Nat.ble (2 ^ n) (cy + 1)))) = true ↔
    ∃ i j : Bool, (cx, cy) = (2 ^ n - 1 + b2n i, 2 ^ n - 1 + b2n j)
  rw [hp]
  show _ ↔ ∃ i j : Bool, (cx, cy) = (p + b2n i, p + b2n j)
  constructor
  · intro h
    obtain ⟨h1, h'⟩ := and_true_split h
    obtain ⟨h2, h''⟩ := and_true_split h'
    obtain ⟨h3, h4⟩ := and_true_split h''
    obtain ⟨i, hi⟩ := between_center (Nat.le_of_succ_le_succ (Nat.le_of_ble_eq_true h2))
      (Nat.le_of_ble_eq_true h1)
    obtain ⟨j, hj⟩ := between_center (Nat.le_of_succ_le_succ (Nat.le_of_ble_eq_true h4))
      (Nat.le_of_ble_eq_true h3)
    exact ⟨i, j, by rw [hi, hj]⟩
  · intro ⟨i, j, hij⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
    rw [ble_center_up, ble_center_up]
    show (Nat.ble (p + 1) (p + b2n i + 1) && (true && Nat.ble (p + 1) (p + b2n j + 1))) = true
    rw [ble_add_right p (p + b2n i) 1, ble_add_right p (p + b2n j) 1, ble_center, ble_center]
    rfl

/-- **The bridge touches the middle from the three non-deficient quadrants.**
    It covers the centre cell of quadrant `q` exactly when `q` is not the
    deficient quadrant (`inTromino` from `Base`). -/
theorem bridge_covers_centerCell (n : Nat) (mi mj i j : Bool) :
    covers (bridge n (mi, mj)) (centerCell n (i, j)).1 (centerCell n (i, j)).2 =
      inTromino (mi, mj) (i, j) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  show (Nat.ble (2 ^ n - 1) (2 ^ n - 1 + b2n i) && (Nat.ble (2 ^ n - 1 + b2n i) (2 ^ n - 1 + 1) &&
      (Nat.ble (2 ^ n - 1) (2 ^ n - 1 + b2n j) && (Nat.ble (2 ^ n - 1 + b2n j) (2 ^ n - 1 + 1) &&
        !(Nat.beq (2 ^ n - 1 + b2n i) (2 ^ n - 1 + b2n mi) &&
          Nat.beq (2 ^ n - 1 + b2n j) (2 ^ n - 1 + b2n mj)))))) = _
  rw [hp]
  show (Nat.ble p (p + b2n i) && (Nat.ble (p + b2n i) (p + 1) &&
      (Nat.ble p (p + b2n j) && (Nat.ble (p + b2n j) (p + 1) &&
        !(Nat.beq (p + b2n i) (p + b2n mi) && Nat.beq (p + b2n j) (p + b2n mj)))))) = _
  rw [ble_center, ble_center, ble_center_up, ble_center_up, beq_center, beq_center]
  rfl

/-- The bridge covers nothing but centre cells. -/
theorem bridge_only_center (n : Nat) (qm : Cell) (cx cy : Nat)
    (h : covers (bridge n qm) cx cy = true) : ∃ i j : Bool, (cx, cy) = centerCell n (i, j) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  have h' : (Nat.ble (2 ^ n - 1) cx && (Nat.ble cx (2 ^ n - 1 + 1) &&
      (Nat.ble (2 ^ n - 1) cy && (Nat.ble cy (2 ^ n - 1 + 1) && _)))) = true := h
  rw [hp] at h'
  obtain ⟨h1, h'⟩ := and_true_split h'
  obtain ⟨h2, h'⟩ := and_true_split h'
  obtain ⟨h3, h'⟩ := and_true_split h'
  obtain ⟨h4, _⟩ := and_true_split h'
  obtain ⟨i, hi⟩ := between_center (Nat.le_of_ble_eq_true h1) (Nat.le_of_ble_eq_true h2)
  obtain ⟨j, hj⟩ := between_center (Nat.le_of_ble_eq_true h3) (Nat.le_of_ble_eq_true h4)
  refine ⟨i, j, ?_⟩
  show (cx, cy) = (2 ^ n - 1 + b2n i, 2 ^ n - 1 + b2n j)
  rw [hp, hi, hj]

/-- Non-vacuity on the 4×4 board (n = 1): the centre cells are (1,1), (2,1),
    (1,2), (2,2), and the bridge for a hole in quadrant (0,0) covers the last three. -/
theorem center_4x4 :
    centerCell 1 (false, false) = (1, 1) ∧ centerCell 1 (true, false) = (2, 1) ∧
    centerCell 1 (false, true) = (1, 2) ∧ centerCell 1 (true, true) = (2, 2) ∧
    covers (bridge 1 (false, false)) 1 1 = false ∧ covers (bridge 1 (false, false)) 2 1 = true ∧
    covers (bridge 1 (false, false)) 1 2 = true ∧ covers (bridge 1 (false, false)) 2 2 = true := by
  decide

/-! ### The bridge read at a decomposed cell -/

/-- Whether local coordinate `l` of half `a` is the centre-adjacent one
    (`p` in the lower half, `0` in the upper half, for `S = p + 1`). -/
def isC (p : Nat) (a : Bool) (l : Nat) : Bool := Nat.beq l (cond a 0 p)

theorem bridge_axis (p : Nat) (a : Bool) {l : Nat} (hl : l < p + 1) :
    (Nat.ble p (l + offS (p + 1) a) && Nat.ble (l + offS (p + 1) a) (p + 1)) = isC p a l := by
  cases a with
  | false =>
    show (Nat.ble p l && Nat.ble l (p + 1)) = Nat.beq l p
    rw [ble_true_of_le (Nat.le_succ_of_le (Nat.le_of_lt_succ hl)), Bool.and_true]
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hl) with
    | inl h => rw [h, beq_self']; exact ble_true_of_le (Nat.le_refl p)
    | inr h => rw [ble_false_of_lt h, beq_false_of_ne (Nat.ne_of_lt h)]
  | true =>
    show (Nat.ble p (l + (p + 1)) && Nat.ble (l + (p + 1)) (p + 1)) = Nat.beq l 0
    rw [ble_true_of_le (Nat.le_trans (Nat.le_succ p) (Nat.le_add_left (p + 1) l))]
    cases l with
    | zero => rw [Nat.zero_add]; exact ble_true_of_le (Nat.le_refl (p + 1))
    | succ l =>
      have h : p + 1 < l + 1 + (p + 1) := by
        rw [Nat.add_right_comm l 1 (p + 1)]
        exact Nat.succ_le_succ (Nat.le_add_left (p + 1) l)
      rw [ble_false_of_lt h]
      rfl

theorem bridge_axis_miss (p : Nat) (a m : Bool) {l : Nat} (hl : l < p + 1) :
    Nat.beq (l + offS (p + 1) a) (p + b2n m) = (isC p a l && (m == a)) := by
  cases a <;> cases m
  · show Nat.beq l p = (Nat.beq l p && true); rw [Bool.and_true]
  · show Nat.beq l (p + 1) = (Nat.beq l p && false)
    rw [Bool.and_false]; exact beq_false_of_ne (Nat.ne_of_lt hl)
  · show Nat.beq (l + (p + 1)) p = (Nat.beq l 0 && false)
    rw [Bool.and_false]
    exact beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self p)
      (Nat.le_add_left (p + 1) l)))
  · show Nat.beq (l + (p + 1)) (p + 1) = (Nat.beq l 0 && true)
    rw [Bool.and_true]
    exact (congrArg (Nat.beq (l + (p + 1))) (Nat.zero_add (p + 1)).symm).trans
      (beq_add_right l 0 (p + 1))

theorem regroup5 (a b c d e : Bool) :
    (a && (b && (c && (d && e)))) = ((a && b) && ((c && d) && e)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem bridge_bool : ∀ cA cB a a' b b' : Bool,
    ((cA) && ((cB) && !((cA && (a == a')) && (cB && (b == b'))))) =
      ((cA && cB) && !(cellEq (a', b') (a, b))) := by
  decide

/-- **The bridge at a decomposed cell.** It covers the cell exactly when the
    cell is the centre-adjacent cell of its quadrant and that quadrant is not
    the deficient one. -/
theorem covers_bridge (p : Nat) (a b a' b' : Bool) {lx ly : Nat}
    (hlx : lx < p + 1) (hly : ly < p + 1) :
    covers (bridgeS (p + 1) (a, b)) (lx + offS (p + 1) a') (ly + offS (p + 1) b') =
      ((isC p a' lx && isC p b' ly) && !(cellEq (a', b') (a, b))) := by
  show (Nat.ble p (lx + offS (p + 1) a') && (Nat.ble (lx + offS (p + 1) a') (p + 1) &&
      (Nat.ble p (ly + offS (p + 1) b') && (Nat.ble (ly + offS (p + 1) b') (p + 1) &&
        !(Nat.beq (lx + offS (p + 1) a') (p + b2n a) &&
          Nat.beq (ly + offS (p + 1) b') (p + b2n b)))))) = _
  rw [regroup5, bridge_axis p a' hlx, bridge_axis p b' hly,
    bridge_axis_miss p a' a hlx, bridge_axis_miss p b' b hly]
  exact bridge_bool _ _ a a' b b'

/-! ## §14 The recursive tiling -/

/-- The four quadrant sub-lists, in a fixed order. -/
def concat4 {α : Type} (F : Cell → List α) : List α :=
  F (false, false) ++ F (false, true) ++ F (true, false) ++ F (true, true)

/-- The hole handed to quadrant `q`, in that quadrant's own coordinates: the
    original hole if `q` is deficient, otherwise the bridge's cell in `q`. -/
def subHoleS (S : Nat) (qm q : Cell) (hx hy : Nat) : Nat × Nat :=
  cond (cellEq q qm) (hx - offS S q.1, hy - offS S q.2)
    (cond q.1 0 (S - 1), cond q.2 0 (S - 1))

/-- The tiling of the `2^n` board with hole `(hx, hy)`. -/
def tile : Nat → Nat → Nat → List Tromino
  | 0, _, _ => []
  | n + 1, hx, hy =>
    bridgeS (2 ^ n) (quadS (2 ^ n) hx hy) ::
      concat4 (fun q =>
        (tile n (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).1
            (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).2).map
          (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2)))

/-! ### Counting over the four quadrants -/

theorem cov_concat4 (F : Cell → List Tromino) (cx cy : Nat) :
    cov (concat4 F) cx cy =
      cov (F (false, false)) cx cy + cov (F (false, true)) cx cy +
        cov (F (true, false)) cx cy + cov (F (true, true)) cx cy := by
  show cov (F (false, false) ++ F (false, true) ++ F (true, false) ++ F (true, true)) cx cy = _
  rw [cov_append, cov_append, cov_append]

theorem cov_concat4_zero (F : Cell → List Tromino) (cx cy : Nat)
    (h : ∀ q, cov (F q) cx cy = 0) : cov (concat4 F) cx cy = 0 := by
  rw [cov_concat4, h, h, h, h]

/-- Exactly one quadrant contributes. -/
theorem cov_concat4_select (F : Cell → List Tromino) (V : Cell → Nat) (qc : Cell) (cx cy : Nat)
    (h : ∀ q, cov (F q) cx cy = cond (cellEq q qc) (V q) 0) :
    cov (concat4 F) cx cy = V qc := by
  rw [cov_concat4, h, h, h, h]
  obtain ⟨a, b⟩ := qc
  cases a <;> cases b
  · rfl
  · exact Nat.zero_add _
  · show 0 + V (true, false) + 0 = V (true, false); exact Nat.zero_add _
  · exact Nat.zero_add _

/-! ### The sub-holes -/

theorem sub_off_cancel (S k : Nat) (b : Bool) : (k + offS S b) - offS S b = k :=
  add_sub_cancel'' k (offS S b)

theorem subHole_lt (p : Nat) (a b : Bool) (q : Cell) {kx ky : Nat}
    (hkx : kx < p + 1) (hky : ky < p + 1) :
    (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).1 < p + 1 ∧
    (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).2 < p + 1 := by
  obtain ⟨q1, q2⟩ := q
  cases q1 <;> cases q2 <;> cases a <;> cases b <;> refine ⟨?_, ?_⟩
  all_goals first
    | exact hkx
    | exact hky
    | exact Nat.lt_succ_self p
    | exact Nat.zero_lt_succ p
    | (show (kx + offS (p + 1) true) - offS (p + 1) true < p + 1
       rw [sub_off_cancel]; exact hkx)
    | (show (ky + offS (p + 1) true) - offS (p + 1) true < p + 1
       rw [sub_off_cancel]; exact hky)

/-- The sub-hole as the local cell of quadrant `qc` sees it: the true hole's
    local position if `qc` is deficient, otherwise the centre-adjacent cell. -/
theorem subHole_beq (p : Nat) (a b a' b' : Bool) (kx ky lx ly : Nat) :
    (Nat.beq lx (subHoleS (p + 1) (a, b) (a', b') (kx + offS (p + 1) a) (ky + offS (p + 1) b)).1 &&
      Nat.beq ly (subHoleS (p + 1) (a, b) (a', b') (kx + offS (p + 1) a) (ky + offS (p + 1) b)).2) =
    cond (cellEq (a', b') (a, b)) (Nat.beq lx kx && Nat.beq ly ky) (isC p a' lx && isC p b' ly) := by
  cases a <;> cases b <;> cases a' <;> cases b'
  all_goals first
    | rfl
    | (show (Nat.beq lx ((kx + offS (p + 1) true) - offS (p + 1) true) &&
          Nat.beq ly ((ky + offS (p + 1) _) - offS (p + 1) _)) = _
       rw [sub_off_cancel, sub_off_cancel]; rfl)
    | (show (Nat.beq lx ((kx + offS (p + 1) _) - offS (p + 1) _) &&
          Nat.beq ly ((ky + offS (p + 1) _) - offS (p + 1) _)) = _
       rw [sub_off_cancel, sub_off_cancel]; rfl)

/-- Equality at the big board, between two decomposed cells. -/
theorem beq_decomposed (S : Nat) (a a' : Bool) {lx kx : Nat} (hlx : lx < S) (hkx : kx < S) :
    Nat.beq (lx + offS S a') (kx + offS S a) = ((a' == a) && Nat.beq lx kx) := by
  cases a <;> cases a'
  · rfl
  · show Nat.beq (lx + S) kx = false
    exact beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hkx (Nat.le_add_left S lx)))
  · show Nat.beq lx (kx + S) = false
    exact beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlx (Nat.le_add_left S kx)))
  · exact beq_add_right lx kx S

theorem decomposed_lt (S : Nat) (a : Bool) {l : Nat} (hl : l < S) : l + offS S a < S + S := by
  cases a with
  | false => exact Nat.lt_of_lt_of_le hl (Nat.le_add_right S S)
  | true => exact Nat.add_lt_add_right hl S

/-- The final count, as a Bool identity decided over its six bits. -/
theorem final_identity : ∀ cA cB ea eb u v : Bool,
    cond ((cA && cB) && !(ea && eb)) 1 0 + cond (!(cond (ea && eb) (u && v) (cA && cB))) 1 0 =
      cond (!((ea && u) && (eb && v))) 1 0 := by
  decide

/-! ### The theorem -/

/-- Base case: the 1×1 board with its one cell as the hole needs no trominoes. -/
theorem tile_correct_zero (hx hy : Nat) (hhx : hx < 2 ^ 0) (hhy : hy < 2 ^ 0) :
    Tiles 0 (tile 0 hx hy) hx hy := by
  intro cx cy
  show 0 = cond (onBoard 1 cx cy && !(Nat.beq cx hx && Nat.beq cy hy)) 1 0
  have h0 : hx = 0 := Nat.le_antisymm (Nat.le_of_lt_succ hhx) (Nat.zero_le _)
  have h0' : hy = 0 := Nat.le_antisymm (Nat.le_of_lt_succ hhy) (Nat.zero_le _)
  subst h0 h0'
  cases cx with
  | zero =>
    cases cy with
    | zero => rfl
    | succ cy =>
      show 0 = cond ((true && Nat.blt (cy + 1) 1) && _) 1 0
      rw [blt_false_of_le (Nat.succ_le_succ (Nat.zero_le cy))]; rfl
  | succ cx =>
    show 0 = cond ((Nat.blt (cx + 1) 1 && _) && _) 1 0
    rw [blt_false_of_le (Nat.succ_le_succ (Nat.zero_le cx))]; rfl

/-- Inductive step: four correct sub-tilings and the bridge give a correct tiling. -/
theorem tile_correct_step (n : Nat)
    (ih : ∀ hx hy : Nat, hx < 2 ^ n → hy < 2 ^ n → Tiles n (tile n hx hy) hx hy)
    (hx hy : Nat) (hhx : hx < 2 ^ (n + 1)) (hhy : hy < 2 ^ (n + 1)) :
    Tiles (n + 1) (tile (n + 1) hx hy) hx hy := by
  intro cx cy
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  rw [two_pow_succ_eq, hp] at hhx hhy
  -- the hole, written node-first: local cell plus the offset of its quadrant
  obtain ⟨a, kx, hkx, rfl, hax⟩ := split_on (p + 1) hx hhx
  obtain ⟨b, ky, hky, rfl, hay⟩ := split_on (p + 1) hy hhy
  -- the four sub-tilings, correct by induction
  have hT : ∀ q : Cell, TilesS (p + 1)
      (tile n (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).1
        (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).2)
      (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).1
      (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).2 := by
    intro q
    have hb := subHole_lt p a b q hkx hky
    have h := ih _ _ (hp ▸ hb.1) (hp ▸ hb.2)
    have h' : TilesS (2 ^ n) _ _ _ := h
    rw [hp] at h'
    exact h'
  -- unfold one level of the recursion
  show cond (covers (bridgeS (2 ^ n) (quadS (2 ^ n) (kx + offS (p + 1) a) (ky + offS (p + 1) b)))
        cx cy) 1 0 +
      cov (concat4 (fun q =>
        (tile n (subHoleS (2 ^ n) (quadS (2 ^ n) (kx + offS (p + 1) a) (ky + offS (p + 1) b)) q
              (kx + offS (p + 1) a) (ky + offS (p + 1) b)).1
            (subHoleS (2 ^ n) (quadS (2 ^ n) (kx + offS (p + 1) a) (ky + offS (p + 1) b)) q
              (kx + offS (p + 1) a) (ky + offS (p + 1) b)).2).map
          (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2)))) cx cy =
    cond (onBoard (2 ^ (n + 1)) cx cy &&
      !(Nat.beq cx (kx + offS (p + 1) a) && Nat.beq cy (ky + offS (p + 1) b))) 1 0
  rw [two_pow_succ_eq, hp]
  have hq : quadS (p + 1) (kx + offS (p + 1) a) (ky + offS (p + 1) b) = (a, b) := by
    show (Nat.ble (p + 1) (kx + offS (p + 1) a), Nat.ble (p + 1) (ky + offS (p + 1) b)) = (a, b)
    rw [hax, hay]
  rw [hq]
  -- now locate the cell
  cases Nat.lt_or_ge cx ((p + 1) + (p + 1)) with
  | inr hcx =>
    -- off the board in x: nothing covers it
    have hbr : covers (bridgeS (p + 1) (a, b)) cx cy = false := by
      show (Nat.ble p cx && (Nat.ble cx (p + 1) && _)) = false
      rw [ble_false_of_lt (Nat.lt_of_lt_of_le
        (Nat.add_lt_add_left (Nat.zero_lt_succ p) (p + 1)) hcx)]
      exact Bool.and_false _
    rw [hbr, cov_concat4_zero _ cx cy (fun q => by
      obtain ⟨l, hl, hle⟩ := split_far (p + 1) cx hcx q.1
      rw [hle]
      exact cov_far_x (hT q) _ _ hl cy)]
    show 0 = cond ((Nat.blt cx ((p + 1) + (p + 1)) && _) && _) 1 0
    rw [blt_false_of_le hcx]
    rfl
  | inl hcx =>
    cases Nat.lt_or_ge cy ((p + 1) + (p + 1)) with
    | inr hcy =>
      -- off the board in y
      have hbr : covers (bridgeS (p + 1) (a, b)) cx cy = false := by
        show (Nat.ble p cx && (Nat.ble cx (p + 1) && (Nat.ble p cy && (Nat.ble cy (p + 1) && _)))) = false
        rw [ble_false_of_lt (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (Nat.zero_lt_succ p) (p + 1)) hcy)]
        cases Nat.ble p cx <;> cases Nat.ble cx (p + 1) <;> cases Nat.ble p cy <;> rfl
      rw [hbr, cov_concat4_zero _ cx cy (fun q => by
        obtain ⟨l, hl, hle⟩ := split_far (p + 1) cy hcy q.2
        rw [hle]
        exact cov_far_y (hT q) _ _ cx hl)]
      show 0 = cond ((Nat.blt cx ((p + 1) + (p + 1)) && Nat.blt cy ((p + 1) + (p + 1))) && _) 1 0
      rw [blt_false_of_le hcy, Bool.and_false]
      rfl
    | inl hcy =>
      -- on the board: write the cell node-first too
      obtain ⟨a', lx, hlx, rfl, _⟩ := split_on (p + 1) cx hcx
      obtain ⟨b', ly, hly, rfl, _⟩ := split_on (p + 1) cy hcy
      rw [covers_bridge p a b a' b' hlx hly,
        cov_concat4_select _ (fun q => cov (tile n
            (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).1
            (subHoleS (p + 1) (a, b) q (kx + offS (p + 1) a) (ky + offS (p + 1) b)).2) lx ly)
          (a', b') _ _ (fun q => cov_sub_cell (hT q) q a' b' hlx hly),
        hT (a', b') lx ly, onBoard_true hlx hly, subHole_beq,
        onBoard_true (decomposed_lt (p + 1) a' hlx) (decomposed_lt (p + 1) b' hly),
        beq_decomposed (p + 1) a a' hlx hkx, beq_decomposed (p + 1) b b' hly hky]
      exact final_identity _ _ _ _ _ _


/-- **Tiling theorem.** For every `n` and every hole on the `2^n × 2^n` board,
    `tile n hx hy` covers every other cell exactly once and nothing else. -/
theorem tile_correct (n : Nat) :
    ∀ hx hy : Nat, hx < 2 ^ n → hy < 2 ^ n → Tiles n (tile n hx hy) hx hy :=
  Nat.rec (motive := fun n => ∀ hx hy : Nat, hx < 2 ^ n → hy < 2 ^ n → Tiles n (tile n hx hy) hx hy)
    tile_correct_zero (fun n ih => tile_correct_step n ih) n

/-! ### Size of the tiling -/

/-- Number of trominoes: `f 0 = 0`, `f (n+1) = 4 f n + 1`. -/
def tcount : Nat → Nat
  | 0 => 0
  | n + 1 => 4 * tcount n + 1

/-- Length of an append, by induction (core's version depends on `propext`). -/
theorem length_append' {α : Type} (A B : List α) : (A ++ B).length = A.length + B.length :=
  List.rec (motive := fun A => (A ++ B).length = A.length + B.length) (Nat.zero_add _).symm
    (fun _ A ih =>
      (congrArg (· + 1) ih).trans (Nat.succ_add A.length B.length).symm)
    A

/-- Length of a map, by induction (core's version depends on `propext`). -/
theorem length_map' {α β : Type} (f : α → β) (A : List α) : (A.map f).length = A.length :=
  List.rec (motive := fun A => (A.map f).length = A.length) rfl
    (fun _ _ ih => congrArg (· + 1) ih) A

/-- `t + t + t + t = 4 t`, from `Nat.mul_succ` alone. -/
theorem four_mul (t : Nat) : t + t + t + t = 4 * t :=
  have h0 : t + t + t + t = 0 + t + t + t + t :=
    congrArg (· + t) (congrArg (· + t) (congrArg (· + t) (Nat.zero_add t).symm))
  have h1 : 0 + t + t + t + t = t * 4 := rfl
  h0.trans (h1.trans (Nat.mul_comm t 4))

theorem length_concat4 {α : Type} (F : Cell → List α) :
    (concat4 F).length = (F (false, false)).length + (F (false, true)).length +
      (F (true, false)).length + (F (true, true)).length := by
  show (F (false, false) ++ F (false, true) ++ F (true, false) ++ F (true, true)).length = _
  rw [length_append', length_append', length_append']

theorem tile_length (n : Nat) : ∀ hx hy : Nat, (tile n hx hy).length = tcount n := by
  induction n with
  | zero => intro hx hy; rfl
  | succ n ih =>
    intro hx hy
    show List.length (concat4 (α := Tromino) _) + 1 = 4 * tcount n + 1
    rw [length_concat4, length_map', length_map', length_map', length_map', ih, ih, ih, ih]
    exact congrArg (· + 1) (four_mul (tcount n))

/-- **Area closes.** `3 · (number of trominoes) + 1 = 4^n`, by Theorem 4 at
    every scale. -/
theorem area_step (t m : Nat) (ih : 3 * t + 1 = 4 ^ m) :
    3 * (4 * t + 1) + 1 = 4 ^ (m + 1) :=
  have h1 : 3 * (4 * t + 1) + 1 = 4 * (3 * t + 1) := (scale_bisection_step t).symm
  have h2 : 4 * (3 * t + 1) = 4 * 4 ^ m := congrArg (fun z => 4 * z) ih
  have h3 : 4 * 4 ^ m = 4 ^ m * 4 := Nat.mul_comm 4 (4 ^ m)
  have h4 : 4 ^ m * 4 = 4 ^ (m + 1) := (Nat.pow_succ (n := 4) (m := m)).symm
  h1.trans (h2.trans (h3.trans h4))

theorem area_identity (n : Nat) : 3 * tcount n + 1 = 4 ^ n :=
  Nat.rec (motive := fun n => 3 * tcount n + 1 = 4 ^ n) rfl
    (fun m ih => area_step (tcount m) m ih) n

theorem tile_area (n hx hy : Nat) : 3 * (tile n hx hy).length + 1 = 4 ^ n := by
  rw [tile_length]; exact area_identity n

/-! ### Non-vacuity -/

/-- The 2×2 board with hole (0,0) is tiled by the single bridge. -/
theorem tile_2x2_witness : tile 1 0 0 = [⟨0, 0, (false, false)⟩] := by decide

/-- The 8×8 board with hole (5, 2), checked cell by cell by the kernel,
    including a margin of cells off the board. -/
theorem tile_8x8_witness :
    ∀ cx, cx < 10 → ∀ cy, cy < 10 →
      cov (tile 3 5 2) cx cy =
        cond (onBoard 8 cx cy && !(Nat.beq cx 5 && Nat.beq cy 2)) 1 0 := by
  decide

/-! ## §15 Necessity of the tiling hypotheses -/

theorem ind_le_00 (t : Tromino) :
    cond (covers t 0 0) 1 0 ≤ cond (covers t 1 0) 1 0 + cond (covers t 0 1) 1 0 := by
  obtain ⟨x, y, ⟨mx, my⟩⟩ := t
  cases x with
  | succ x => exact Nat.zero_le _
  | zero =>
    cases y with
    | succ y => exact Nat.zero_le _
    | zero => cases mx <;> cases my <;> decide

/-- Rearranging two sums (`Nat.add_add_add_comm` is axiom-free). -/
theorem cov_le_00 (T : List Tromino) : cov T 0 0 ≤ cov T 1 0 + cov T 0 1 :=
  List.rec (motive := fun T => cov T 0 0 ≤ cov T 1 0 + cov T 0 1) (Nat.le_refl 0)
    (fun t _ ih =>
      Nat.le_trans (Nat.add_le_add (ind_le_00 t) ih) (Nat.le_of_eq (Nat.add_add_add_comm _ _ _ _)))
    T

/-- **The hole must lie on the board.** With `n = 0` and the hole at `(1, 0)`,
    off the 1×1 board, no list of trominoes meets the specification: any
    tromino covering (0,0) also covers (1,0) or (0,1). -/
theorem tiling_needs_hole_on_board : ¬ ∃ T, Tiles 0 T 1 0 := by
  intro ⟨T, hT⟩
  have h00 : cov T 0 0 = 1 := hT 0 0
  have h10 : cov T 1 0 = 0 := hT 1 0
  have h01 : cov T 0 1 = 0 := hT 0 1
  have h := cov_le_00 T
  rw [h00, h10, h01] at h
  exact Nat.not_succ_le_zero 0 h

theorem ind_le_10 (t : Tromino) :
    cond (covers t 1 0) 1 0 ≤
      cond (covers t 0 0) 1 0 + cond (covers t 1 1) 1 0 +
      cond (covers t 2 0) 1 0 + cond (covers t 2 1) 1 0 := by
  obtain ⟨x, y, ⟨mx, my⟩⟩ := t
  cases x with
  | zero =>
    cases y with
    | succ y => exact Nat.zero_le _
    | zero => cases mx <;> cases my <;> decide
  | succ x =>
    cases x with
    | zero =>
      cases y with
      | succ y => exact Nat.zero_le _
      | zero => cases mx <;> cases my <;> decide
    | succ x => exact Nat.zero_le _

/-- Regrouping two four-term sums. -/
theorem add4_shuffle (a b c d A B C D : Nat) :
    (a + b + c + d) + (A + B + C + D) = (a + A) + (b + B) + (c + C) + (d + D) := by
  rw [Nat.add_add_add_comm (a + b + c) d (A + B + C) D,
    Nat.add_add_add_comm (a + b) c (A + B) C, Nat.add_add_add_comm a b A B]

theorem cov_le_10 (T : List Tromino) :
    cov T 1 0 ≤ cov T 0 0 + cov T 1 1 + cov T 2 0 + cov T 2 1 :=
  List.rec (motive := fun T => cov T 1 0 ≤ cov T 0 0 + cov T 1 1 + cov T 2 0 + cov T 2 1)
    (Nat.le_refl 0)
    (fun t _ ih =>
      Nat.le_trans (Nat.add_le_add (ind_le_10 t) ih) (Nat.le_of_eq (add4_shuffle _ _ _ _ _ _ _ _)))
    T

/-- **Exactly one hole.** On the 2×2 board with both cells of D1 removed,
    (0,0) and (1,1), no list of trominoes covers the remaining D2 cells once
    each and nothing else: any tromino covering (1,0) also covers a removed
    cell or a cell off the board. -/
theorem tiling_needs_single_hole :
    ¬ ∃ T : List Tromino, ∀ cx cy : Nat,
      cov T cx cy = cond (onBoard 2 cx cy && !(Nat.beq cx 0 && Nat.beq cy 0) &&
        !(Nat.beq cx 1 && Nat.beq cy 1)) 1 0 := by
  intro ⟨T, hT⟩
  have h10 : cov T 1 0 = 1 := hT 1 0
  have h00 : cov T 0 0 = 0 := hT 0 0
  have h11 : cov T 1 1 = 0 := hT 1 1
  have h20 : cov T 2 0 = 0 := hT 2 0
  have h21 : cov T 2 1 = 0 := hT 2 1
  have h := cov_le_10 T
  rw [h10, h00, h11, h20, h21] at h
  exact Nat.not_succ_le_zero 0 h

end LTromino

