import LTromino.Tiling

/-!
# LTromino.Equivariance — the tiling transforms with its hole, at every scale

The eight symmetries `Sym` of the 2×2 (Base §3) act on the `2^n × 2^n` board:
optionally swap the two coordinates, then flip x to `2^n − 1 − x` and/or y to
`2^n − 1 − y`. They act on a tromino by moving its 2×2 block the same way and
moving its missing corner by the *same* `Sym` acting on `Cell`.

Main theorem (`tile_equivariant`): for every scale `n`, every symmetry `g` and
every hole, the tiling of the transformed hole is the transformed tiling, up to
the order in which the four quadrants are listed:

    tile n (g · hole)  ~  (tile n hole).map (g · ·)

`~` is `List.Perm`: the same trominoes, each the same number of times. The
proof follows the recursion: the bridge maps to the bridge, each quadrant's
sub-hole maps to the sub-hole of the image quadrant, and the four sub-tilings
are carried to the four image quadrants by the induction hypothesis.
-/

namespace LTromino

/-! ## §14 The action on the board and on trominoes -/

/-- Flip a coordinate at side length `N`, when the bit is set. -/
def flipAt (N : Nat) (b : Bool) (x : Nat) : Nat := if b then N - 1 - x else x

/-- A symmetry acting on board cell `(x, y)` of the `2^n × 2^n` board. -/
def actB (n : Nat) (g : Sym) (x y : Nat) : Nat × Nat :=
  (flipAt (2 ^ n) g.a (if g.s then y else x), flipAt (2 ^ n) g.b (if g.s then x else y))

/-- A symmetry acting on a tromino: its block's lower-left corner goes where the
    image block's lower-left corner is (`2^n − 2 − x` under a flip, since the
    block is two cells wide), and its missing corner moves by the same `g`. -/
def actT (n : Nat) (g : Sym) (t : Tromino) : Tromino :=
  ⟨flipAt (2 ^ n - 1) g.a (if g.s then t.y else t.x),
   flipAt (2 ^ n - 1) g.b (if g.s then t.x else t.y),
   act g t.miss⟩

/-- A tromino whose 2×2 block lies on the `2^n` board. -/
def Inside (n : Nat) (t : Tromino) : Prop := t.x + 2 ≤ 2 ^ n ∧ t.y + 2 ≤ 2 ^ n

/-! ## §15 The action respects covering -/

/-- `Nat.ble` as `decide`, for `simp`. -/
theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b with
  | true => exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm
  | false =>
    exact (decide_eq_false (fun h' => Bool.noConfusion (h.symm.trans (ble_true_of_le h')))).symm

/-- Reading `Nat.beq … = false` as `≠`, for `simp`. -/
theorem beq_false_iff_ne (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h e; rw [e, beq_self'] at h; exact Bool.noConfusion h
  · exact beq_false_of_ne

/-- **Covering is equivariant.** For a tromino on the board and a board cell,
    `g · t` covers `g · c` exactly when `t` covers `c`. -/
theorem covers_actT (n : Nat) (g : Sym) (t : Tromino) (ht : Inside n t)
    (cx cy : Nat) (hx : cx < 2 ^ n) (hy : cy < 2 ^ n) :
    covers (actT n g t) (actB n g cx cy).1 (actB n g cx cy).2 = covers t cx cy := by
  obtain ⟨s, a, b⟩ := g
  obtain ⟨tx, ty, mx, my⟩ := t
  simp only [Inside] at ht
  simp only [covers, actT, actB]
  generalize 2 ^ n = N at ht hx hy ⊢
  rw [Bool.eq_iff_iff]
  cases s <;> cases a <;> cases b <;> cases mx <;> cases my <;>
    simp [flipAt, act, b2n, Nat.ble_eq, beq_false_iff_ne] <;> omega

/-! ## §16 Every tromino of the tiling lies on the board (no hypothesis on the hole) -/

theorem tile_inside (n : Nat) : ∀ hx hy : Nat, ∀ t ∈ tile n hx hy, Inside n t := by
  induction n with
  | zero => intro hx hy t ht; simp [tile] at ht
  | succ n ih =>
    intro hx hy t ht
    have hs := two_pow_pos' n
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    simp only [tile, concat4, List.mem_cons, List.mem_append, List.mem_map] at ht
    simp only [Inside, h2]
    rcases ht with rfl | (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    · simp only [bridgeS]; omega
    all_goals
      have := ih _ _ u hu
      simp only [Inside] at this
      simp [shift, offS]
      omega

/-! ## §17 The four structural facts of the recursion -/

/-- The quadrant of the transformed hole is the transformed quadrant (Base `act`). -/
theorem quadrant_actB (n : Nat) (g : Sym) (hx hy : Nat) :
    quadS (2 ^ n) (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2 =
      act g (quadS (2 ^ n) hx hy) := by
  obtain ⟨s, a, b⟩ := g
  have hs := two_pow_pos' n
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
  simp only [quadS, actB, act, flipAt, h2, ble_eq_decide]
  generalize 2 ^ n = S at hs
  by_cases ex : S ≤ hx <;> by_cases ey : S ≤ hy <;>
    cases s <;> cases a <;> cases b <;>
    simp [ex, ey] <;> omega

/-- The bridge is carried to the bridge of the transformed deficient quadrant. -/
theorem bridge_actT (n : Nat) (g : Sym) (qm : Cell) :
    actT (n + 1) g (bridgeS (2 ^ n) qm) = bridgeS (2 ^ n) (act g qm) := by
  obtain ⟨s, a, b⟩ := g
  have hs := two_pow_pos' n
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
  simp only [actT, bridgeS, flipAt, h2, Tromino.mk.injEq]
  generalize 2 ^ n = S at hs
  cases s <;> cases a <;> cases b <;> simp <;> omega

/-- A tromino placed in quadrant `q` and then transformed at scale `n+1` equals
    the tromino transformed at scale `n` and placed in quadrant `g · q`. -/
theorem shift_actT (n : Nat) (g : Sym) (q : Cell) (t : Tromino) (ht : Inside n t) :
    actT (n + 1) g (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2) t) =
      shift (offS (2 ^ n) (act g q).1) (offS (2 ^ n) (act g q).2) (actT n g t) := by
  obtain ⟨s, a, b⟩ := g
  obtain ⟨qx, qy⟩ := q
  obtain ⟨tx, ty, m⟩ := t
  simp only [Inside] at ht
  have hs := two_pow_pos' n
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
  simp only [actT, shift, offS, act, flipAt, h2, Tromino.mk.injEq]
  generalize 2 ^ n = S at hs ht
  cases s <;> cases a <;> cases b <;> cases qx <;> cases qy <;> simp <;> omega

/-- Cell equality is preserved by every symmetry. -/
theorem cellEq_act : ∀ s a b px py qx qy : Bool,
    cellEq (act ⟨s, a, b⟩ (px, py)) (act ⟨s, a, b⟩ (qx, qy)) = cellEq (px, py) (qx, qy) := by
  decide

/-- The sub-hole handed to quadrant `g · q` of the transformed board is the
    transformed sub-hole of quadrant `q`. -/
theorem subHole_actB (n : Nat) (g : Sym) (q : Cell) (hx hy : Nat) :
    subHoleS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) (act g q)
        (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2 =
      actB n g (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).1
        (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).2 := by
  obtain ⟨s, a, b⟩ := g
  obtain ⟨qx, qy⟩ := q
  have hs := two_pow_pos' n
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
  simp only [subHoleS, quadS, actB, act, flipAt, offS, cellEq, h2, ble_eq_decide]
  by_cases ex : 2 ^ n ≤ hx <;> by_cases ey : 2 ^ n ≤ hy <;>
    cases s <;> cases a <;> cases b <;> cases qx <;> cases qy <;>
    simp [ex, ey] <;> omega

/-! ## §18 Relabelling the four quadrants is a permutation of the listing -/

theorem concat4_act_perm {α : Type} [DecidableEq α] (F : Cell → List α) (g : Sym) :
    (concat4 (fun q => F (act g q))).Perm (concat4 F) := by
  rw [List.perm_iff_count]
  intro a
  obtain ⟨s, a', b⟩ := g
  cases s <;> cases a' <;> cases b <;>
    simp only [concat4, act, List.count_append] <;> simp <;> omega

theorem concat4_perm {α : Type} {F G : Cell → List α} (h : ∀ q, (F q).Perm (G q)) :
    (concat4 F).Perm (concat4 G) :=
  (((h _).append (h _)).append (h _)).append (h _)

/-! ## §19 The equivariance theorem -/

/-- **Equivariance at every scale.** Transforming the hole by any symmetry of
    the square transforms every tromino of the recursive tiling by that same
    symmetry. No hypothesis on the hole is needed. -/
theorem tile_equivariant (n : Nat) :
    ∀ (g : Sym) (hx hy : Nat),
      (tile n (actB n g hx hy).1 (actB n g hx hy).2).Perm ((tile n hx hy).map (actT n g)) := by
  induction n with
  | zero => intro g hx hy; exact List.Perm.refl _
  | succ n ih =>
    intro g hx hy
    -- the two sides, unfolded one level
    let sub (q : Cell) : List Tromino :=
      (tile n (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).1
        (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).2).map (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2))
    have hR : (tile (n + 1) hx hy).map (actT (n + 1) g) =
        bridgeS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) :: concat4 (fun q => (sub q).map (actT (n + 1) g)) := by
      simp only [tile, List.map_cons, List.map_append, bridge_actT, concat4, sub]
    have hL : tile (n + 1) (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2 =
        bridgeS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) ::
          concat4 (fun q' =>
            (tile n (subHoleS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) q'
                (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2).1
              (subHoleS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) q'
                (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2).2).map
              (shift (offS (2 ^ n) q'.1) (offS (2 ^ n) q'.2))) := by
      simp only [tile, concat4, quadrant_actB]
    rw [hL, hR]
    refine List.Perm.cons _ ?_
    refine List.Perm.trans (concat4_act_perm _ g).symm (concat4_perm fun q => ?_)
    -- quadrant g·q of the new board against quadrant q of the old one
    simp only [subHole_actB]
    refine ((ih g _ _).map _).trans ?_
    rw [List.map_map, List.map_map]
    refine List.Perm.of_eq (List.map_congr_left fun t ht => ?_)
    exact (shift_actT n g q t (tile_inside n _ _ t ht)).symm

/-! ## §20 Consequences and non-vacuity -/

/-- Coverage counts do not depend on the order of the list. -/
theorem cov_perm {T U : List Tromino} (h : T.Perm U) (cx cy : Nat) : cov T cx cy = cov U cx cy := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp only [cov, ih]
  | swap t u T => simp only [cov]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem cov_map_actT (n : Nat) (g : Sym) (T : List Tromino) (hT : ∀ t ∈ T, Inside n t)
    (cx cy : Nat) (hx : cx < 2 ^ n) (hy : cy < 2 ^ n) :
    cov (T.map (actT n g)) (actB n g cx cy).1 (actB n g cx cy).2 = cov T cx cy := by
  induction T with
  | nil => rfl
  | cons t T ih =>
    simp only [List.map_cons, cov]
    rw [ih (fun u hu => hT u (List.mem_cons_of_mem _ hu)),
      covers_actT n g t (hT t (List.mem_cons_self ..)) cx cy hx hy]

/-- **The coverage picture transforms with the hole.** Each board cell `c` is
    covered by the tiling of `g · hole` exactly as often as `c` itself was by the
    tiling of the hole, read at `g · c`. -/
theorem cov_equivariant (n : Nat) (g : Sym) (hx hy cx cy : Nat)
    (hcx : cx < 2 ^ n) (hcy : cy < 2 ^ n) :
    cov (tile n (actB n g hx hy).1 (actB n g hx hy).2) (actB n g cx cy).1 (actB n g cx cy).2 =
      cov (tile n hx hy) cx cy :=
  (cov_perm (tile_equivariant n g hx hy) _ _).trans
    (cov_map_actT n g _ (tile_inside n hx hy) cx cy hcx hcy)

/-- Non-vacuity on the 4×4 board: the chiral swap (reflection across D1) takes
    hole (1, 2) to hole (2, 1), and the kernel checks the tilings agree. -/
theorem equivariant_4x4_reflD1 :
    actB 2 reflD1 1 2 = (2, 1) ∧
    ((tile 2 2 1).Perm ((tile 2 1 2).map (actT 2 reflD1))) := by
  refine ⟨by decide, ?_⟩
  exact tile_equivariant 2 reflD1 1 2

/-- On the 8×8 board with hole (5, 2), the Phantom Middle π takes the hole to
    (2, 5); every tromino of the image tiling is π of a tromino of the original,
    checked by evaluation. -/
theorem equivariant_8x8_pi :
    actB 3 rot180 5 2 = (2, 5) ∧
    ((tile 3 2 5).all fun t => ((tile 3 5 2).map (actT 3 rot180)).contains t) = true ∧
    (((tile 3 5 2).map (actT 3 rot180)).all fun t => (tile 3 2 5).contains t) = true := by
  decide

/-- Bool-valued permutation check by counting each element (no `Prop` membership). -/
def countEq (T U : List Tromino) : Bool :=
  T.length == U.length && (T ++ U).all fun t => T.count t == U.count t

/-- Exhaustive kernel evaluation on the 4×4 board: for all 8 symmetries and all
    16 holes, the tiling of the transformed hole and the transformed tiling
    contain every tromino the same number of times. -/
theorem equivariant_4x4_exhaustive :
    ([idS, rot90, rot180, rot270, mirrorX, mirrorY, reflD1, reflD2].all fun g =>
      (List.range 4).all fun hx => (List.range 4).all fun hy =>
        countEq (tile 2 (actB 2 g hx hy).1 (actB 2 g hx hy).2) ((tile 2 hx hy).map (actT 2 g))) = true := by
  decide

/-! ## §21 Necessity -/

/-- **Up to order, not equal as lists.** The quadrants are listed in a fixed
    order, which a symmetry permutes, so `Perm` is the precise statement: the
    chiral swap example above is a permutation but not literal list equality. -/
theorem equivariance_not_list_equality :
    tile 2 2 1 ≠ (tile 2 1 2).map (actT 2 reflD1) := by
  decide

/-- A faulty action that moves the block but leaves the missing corner fixed. -/
def actT_keepMiss (n : Nat) (g : Sym) (t : Tromino) : Tromino :=
  ⟨(actT n g t).x, (actT n g t).y, t.miss⟩

/-- A faulty action that flips the block as if it were one cell wide. -/
def actT_oneWide (n : Nat) (g : Sym) (t : Tromino) : Tromino :=
  ⟨flipAt (2 ^ n) g.a (if g.s then t.y else t.x),
   flipAt (2 ^ n) g.b (if g.s then t.x else t.y), act g t.miss⟩

/-- **The missing corner must move by the same symmetry.** Under the D2
    reflection the hole (0,0) of the 2×2 goes to (1,1); keeping the missing
    corner fixed gives a tromino that still misses (0,0), not the tiling. -/
theorem miss_must_move :
    actB 1 reflD2 0 0 = (1, 1) ∧
    tile 1 1 1 ≠ (tile 1 0 0).map (actT_keepMiss 1 reflD2) := by
  decide

/-- **The block moves by `2^n − 2 − x`, not `2^n − 1 − x`.** A tromino is two
    cells wide; flipping its corner as if it were a single cell pushes it one
    step off the board. -/
theorem block_flip_needs_width_two :
    actB 1 mirrorX 0 0 = (1, 0) ∧
    tile 1 1 0 ≠ (tile 1 0 0).map (actT_oneWide 1 mirrorX) := by
  decide

/-- The hole needs no hypothesis: even off the board, truncated subtraction
    clamps the hole the same way on both sides. Here the 2×2 board's hole is
    placed at (3, 0), off the board, and the theorem still applies. -/
theorem equivariant_off_board_hole :
    (tile 1 (actB 1 mirrorX 3 0).1 (actB 1 mirrorX 3 0).2).Perm
      ((tile 1 3 0).map (actT 1 mirrorX)) :=
  tile_equivariant 1 mirrorX 3 0

end LTromino

