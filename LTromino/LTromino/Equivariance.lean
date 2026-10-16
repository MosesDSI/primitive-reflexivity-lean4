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

/-! ## §15 An axiom-free toolkit for lists and for flipping

In Lean 4.33.1 the core lemmas `List.mem_cons`, `List.mem_append`,
`List.mem_map`, `List.Perm.map`, `List.map_map`, `List.map_append`,
`List.map_congr_left`, `List.append_assoc`, `List.perm_append_comm` and the
tactics `simp`, `omega`, `ac_rfl` all bring in
`propext` (and some `Quot.sound` or `Classical.choice`). They are replaced
here by local versions proved by induction, `cases` and `rw`.

Flips are handled discrete-first, as in `Tiling.lean`: a board coordinate is
never compared through a subtraction. It is written as local cell plus the
offset of its half (`split_on`), or as a point beyond the board (`split_far`
style), and the flip is computed on that form. -/

/-- `Nat.ble` as `decide`. -/
theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b with
  | true => exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm
  | false =>
    exact (decide_eq_false (fun h' => Bool.noConfusion (h.symm.trans (ble_true_of_le h')))).symm

/-- Reading `Nat.beq … = false` as `≠`. -/
theorem beq_false_iff_ne (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h e; rw [e, beq_self'] at h; exact Bool.noConfusion h
  · exact beq_false_of_ne

/-! ### Lists -/

theorem mem_cons_inv {α : Type} {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ a ∈ l := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h => exact Or.inr h

theorem mem_append_inv {α : Type} {a : α} :
    ∀ {l₁ l₂ : List α}, a ∈ l₁ ++ l₂ → a ∈ l₁ ∨ a ∈ l₂
  | [], _, h => Or.inr h
  | _ :: _, _, h =>
    (mem_cons_inv h).elim
      (fun e => Or.inl (by rw [e]; exact List.mem_cons_self ..))
      (fun h' => (mem_append_inv h').elim (fun h₁ => Or.inl (List.mem_cons_of_mem _ h₁)) Or.inr)

theorem mem_map_inv {α β : Type} {f : α → β} {b : β} :
    ∀ {l : List α}, b ∈ l.map f → ∃ a, a ∈ l ∧ f a = b
  | [], h => nomatch h
  | a :: _, h =>
    (mem_cons_inv h).elim
      (fun e => ⟨a, List.mem_cons_self .., e.symm⟩)
      (fun h' => match mem_map_inv h' with
        | ⟨a', ha', e⟩ => ⟨a', List.mem_cons_of_mem _ ha', e⟩)

theorem mem_concat4 {α : Type} {F : Cell → List α} {a : α} (h : a ∈ concat4 F) :
    ∃ q, a ∈ F q :=
  (mem_append_inv h).elim
    (fun h => (mem_append_inv h).elim
      (fun h => (mem_append_inv h).elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩))
      (fun h => ⟨_, h⟩))
    (fun h => ⟨_, h⟩)

theorem append_nil' {α : Type} : ∀ l : List α, l ++ [] = l
  | [] => rfl
  | x :: l => congrArg (x :: ·) (append_nil' l)

theorem append_assoc' {α : Type} : ∀ a b c : List α, a ++ b ++ c = a ++ (b ++ c)
  | [], _, _ => rfl
  | x :: a, b, c => congrArg (x :: ·) (append_assoc' a b c)

theorem perm_append_comm' {α : Type} : ∀ a b : List α, (a ++ b).Perm (b ++ a)
  | [], b => List.Perm.of_eq (append_nil' b).symm
  | x :: a, b => ((perm_append_comm' a b).cons x).trans List.perm_middle.symm

theorem map_append' {α β : Type} (f : α → β) : ∀ a b : List α, (a ++ b).map f = a.map f ++ b.map f
  | [], _ => rfl
  | x :: a, b => congrArg (f x :: ·) (map_append' f a b)

theorem map_map' {α β γ : Type} (f : α → β) (g : β → γ) :
    ∀ l : List α, (l.map f).map g = l.map (fun x => g (f x))
  | [] => rfl
  | x :: l => congrArg (g (f x) :: ·) (map_map' f g l)

theorem map_congr' {α β : Type} {f g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.map f = l.map g
  | [], _ => rfl
  | x :: _, h => by
    show f x :: _ = g x :: _
    rw [h x (List.mem_cons_self ..), map_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem perm_map' {α β : Type} (f : α → β) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (l₁.map f).Perm (l₂.map f) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih => exact ih.cons (f x)
  | swap x y l => exact List.Perm.swap (f x) (f y) (l.map f)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem map_concat4 {α β : Type} (f : α → β) (F : Cell → List α) :
    (concat4 F).map f = concat4 (fun q => (F q).map f) := by
  show (F (false, false) ++ F (false, true) ++ F (true, false) ++ F (true, true)).map f = _
  rw [map_append', map_append', map_append']
  rfl

/-! ### Naturals -/

theorem sub_of_add_eq {a b c : Nat} (h : a + b = c) : c - b = a := by
  rw [← h]; exact add_sub_cancel'' a b

/-- Subtracting something at least as large leaves nothing. -/
theorem sub_self_add (a : Nat) : ∀ k, a - (a + k) = 0 := by
  induction a with
  | zero => intro k; exact Nat.zero_sub _
  | succ a ih =>
    intro k
    rw [Nat.add_right_comm a 1 k]
    exact (Nat.succ_sub_succ a (a + k)).trans (ih k)

theorem beq_comm' : ∀ a b : Nat, Nat.beq a b = Nat.beq b a
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | a + 1, b + 1 => beq_comm' a b

theorem le_of_add_eq {l k p : Nat} (h : l + k = p) : k ≤ p := h ▸ Nat.le_add_left k l

/-! ### Flipping on a half and on the whole board (half side `p + 1`) -/

/-- On a half of side `p + 1`, the flip of `l` is its complement `k`, `l + k = p`. -/
theorem flip_small (p l k : Nat) (h : l + k = p) : flipAt (p + 1) true l = k :=
  sub_of_add_eq ((Nat.add_comm k l).trans h)

/-- On the whole board, the flip of `l + offset b` is the complement in the other half. -/
theorem flip_big (p l k : Nat) (b : Bool) (h : l + k = p) :
    flipAt (p + 1 + (p + 1)) true (l + offS (p + 1) b) = k + offS (p + 1) (!b) := by
  cases b with
  | false =>
    show (p + 1 + p) - l = k + (p + 1)
    apply sub_of_add_eq
    rw [Nat.add_comm k (p + 1), Nat.add_assoc, Nat.add_comm k l, h]
  | true =>
    show (p + 1 + p) - (l + (p + 1)) = k
    apply sub_of_add_eq
    rw [← Nat.add_assoc, Nat.add_comm k l, h, Nat.add_comm p (p + 1)]

/-- Beyond the board, the flip is clamped to `0`. -/
theorem flip_far (p j : Nat) : flipAt (p + 1 + (p + 1)) true (p + 1 + (p + 1) + j) = 0 := by
  show (p + 1 + p) - ((p + 1 + p) + 1 + j) = 0
  rw [Nat.add_assoc (p + 1 + p) 1 j]
  exact sub_self_add _ _

theorem ble_decomp (p k : Nat) (c : Bool) (hk : k ≤ p) : Nat.ble (p + 1) (k + offS (p + 1) c) = c := by
  cases c with
  | false => exact ble_false_of_lt (Nat.lt_succ_of_le hk)
  | true => exact ble_true_of_le (Nat.le_add_left (p + 1) k)

theorem ble_far (p j : Nat) : Nat.ble (p + 1) (p + 1 + (p + 1) + j) = true :=
  ble_true_of_le (Nat.le_trans (Nat.le_add_right (p + 1) (p + 1)) (Nat.le_add_right _ j))

/-- **The quadrant bit of a flipped coordinate** is the flipped quadrant bit,
    for every coordinate, on or off the board. -/
theorem ble_flip_board (p z : Nat) (a : Bool) :
    Nat.ble (p + 1) (flipAt (p + 1 + (p + 1)) a z) = (Nat.ble (p + 1) z ^^ a) := by
  cases a with
  | false => exact (Bool.xor_false _).symm
  | true =>
    rw [Bool.xor_true]
    cases Nat.lt_or_ge z (p + 1 + (p + 1)) with
    | inl hz =>
      obtain ⟨b, l, hl, rfl, hb⟩ := split_on (p + 1) z hz
      obtain ⟨k, hk⟩ := Nat.le.dest (Nat.le_of_lt_succ hl)
      rw [flip_big p l k b hk, hb, ble_decomp p k (!b) (le_of_add_eq hk)]
    | inr hz =>
      obtain ⟨j, rfl⟩ := Nat.le.dest hz
      rw [flip_far, ble_far]
      exact ble_false_of_lt (Nat.zero_lt_succ p)

/-- **The local coordinate of a flipped coordinate** is the flipped local
    coordinate, for every coordinate (off the board both sides clamp to 0). -/
theorem sub_flip (p z : Nat) (a : Bool) :
    flipAt (p + 1 + (p + 1)) a z - offS (p + 1) (Nat.ble (p + 1) z ^^ a) =
      flipAt (p + 1) a (z - offS (p + 1) (Nat.ble (p + 1) z)) := by
  cases a with
  | false =>
    show z - offS (p + 1) (Nat.ble (p + 1) z ^^ false) = z - offS (p + 1) (Nat.ble (p + 1) z)
    rw [Bool.xor_false]
  | true =>
    rw [Bool.xor_true]
    cases Nat.lt_or_ge z (p + 1 + (p + 1)) with
    | inl hz =>
      obtain ⟨b, l, hl, rfl, hb⟩ := split_on (p + 1) z hz
      obtain ⟨k, hk⟩ := Nat.le.dest (Nat.le_of_lt_succ hl)
      rw [hb, flip_big p l k b hk, sub_off_cancel, sub_off_cancel, flip_small p l k hk]
    | inr hz =>
      obtain ⟨j, rfl⟩ := Nat.le.dest hz
      rw [flip_far, ble_far]
      show 0 = p - ((p + 1 + (p + 1) + j) - (p + 1))
      rw [Nat.add_right_comm (p + 1) (p + 1) j, add_sub_cancel'', Nat.add_assoc p 1 j, sub_self_add]

/-- The centre-adjacent local coordinate (`p` in the lower half, `0` in the
    upper) flips to the other one. -/
theorem flip_centre_coord (p : Nat) (a c : Bool) :
    flipAt (p + 1) a (cond c 0 p) = cond (c ^^ a) 0 p := by
  cases a <;> cases c
  · rfl
  · rfl
  · exact Nat.sub_self p
  · rfl

/-- The bridge corner `p` is fixed by the block flip on the `2(p+1)` board. -/
theorem flip_center (p : Nat) (a : Bool) : flipAt (p + 1 + (p + 1) - 1) a p = p := by
  cases a with
  | false => rfl
  | true =>
    show (p + 1 + p) - 1 - p = p
    rw [Nat.add_right_comm p 1 p]
    exact add_sub_cancel'' p p

/-- A block placed in a half, then flipped at the next scale, is the flipped
    block placed in the flipped half. -/
theorem flip_shift (p x : Nat) (qb a : Bool) (hx : x + 2 ≤ p + 1) :
    flipAt (p + 1 + (p + 1) - 1) a (x + offS (p + 1) qb) =
      flipAt (p + 1 - 1) a x + offS (p + 1) (qb ^^ a) := by
  cases a with
  | false =>
    show x + offS (p + 1) qb = x + offS (p + 1) (qb ^^ false)
    rw [Bool.xor_false]
  | true =>
    obtain ⟨r, hr⟩ := Nat.le.dest hx
    have hp : x + r + 1 = p := by
      apply Nat.succ.inj
      show x + r + 2 = p + 1
      rw [← Nat.add_right_comm x 2 r]
      exact hr
    have hflip : flipAt (p + 1 - 1) true x = r := by
      show p - 1 - x = r
      rw [← hp]
      show (x + r) - x = r
      rw [Nat.add_comm x r]
      exact add_sub_cancel'' r x
    rw [hflip]
    show (p + 1 + p) - 1 - (x + offS (p + 1) qb) = r + offS (p + 1) (qb ^^ true)
    rw [Nat.add_right_comm p 1 p, Bool.xor_true]
    show (p + p) - (x + offS (p + 1) qb) = r + offS (p + 1) (!qb)
    apply sub_of_add_eq
    cases qb with
    | false =>
      show r + (p + 1) + x = p + p
      rw [Nat.add_comm r (p + 1), Nat.add_assoc, Nat.add_comm r x, Nat.add_right_comm p 1 (x + r),
        Nat.add_assoc p (x + r) 1, hp]
    | true =>
      show r + (x + (p + 1)) = p + p
      rw [← Nat.add_assoc, Nat.add_comm r x, ← Nat.add_assoc, Nat.add_right_comm (x + r) p 1, hp]

/-! ### One axis of `covers` under a flip -/

/-- On one axis, flipping the block and the cell exchanges the two interval
    tests and keeps the missing-corner test. -/
theorem cov_axis (N t c : Nat) (m a : Bool) (ht : t + 2 ≤ N) (hc : c < N) :
    Nat.ble (flipAt (N - 1) a t) (flipAt N a c) = cond a (Nat.ble c (t + 1)) (Nat.ble t c) ∧
    Nat.ble (flipAt N a c) (flipAt (N - 1) a t + 1) = cond a (Nat.ble t c) (Nat.ble c (t + 1)) ∧
    Nat.beq (flipAt N a c) (flipAt (N - 1) a t + b2n (m ^^ a)) = Nat.beq c (t + b2n m) := by
  cases a with
  | false =>
    refine ⟨rfl, rfl, ?_⟩
    show Nat.beq c (t + b2n (m ^^ false)) = Nat.beq c (t + b2n m)
    rw [Bool.xor_false]
  | true =>
    obtain ⟨r, rfl⟩ := Nat.le.dest ht
    obtain ⟨k, hk⟩ := Nat.le.dest hc
    have ht' : flipAt (t + 2 + r - 1) true t = r := by
      show (t + 2 + r) - 1 - 1 - t = r
      rw [Nat.add_right_comm t 2 r]
      show (t + r) - t = r
      rw [Nat.add_comm t r]
      exact add_sub_cancel'' r t
    have hc' : flipAt (t + 2 + r) true c = k := by
      show (t + 2 + r) - 1 - c = k
      rw [← hk, Nat.add_right_comm c 1 k]
      show (c + k) - c = k
      rw [Nat.add_comm c k]
      exact add_sub_cancel'' k c
    have H : k + c = t + 1 + r := by
      apply Nat.succ.inj
      show k + c + 1 = t + 1 + r + 1
      rw [Nat.add_comm k c, Nat.add_right_comm c k 1, hk, Nat.add_right_comm (t + 1) r 1]
    rw [ht', hc']
    refine ⟨?_, ?_, ?_⟩
    · show Nat.ble r k = Nat.ble c (t + 1)
      rw [← ble_add_right r k c, H, Nat.add_comm r c]
      exact ble_add_right c (t + 1) r
    · show Nat.ble k (r + 1) = Nat.ble t c
      rw [← ble_add_right k (r + 1) c, H, Nat.add_comm (r + 1) c, Nat.add_right_comm t 1 r]
      exact ble_add_right t c (r + 1)
    · cases m
      · show Nat.beq k (r + 1) = Nat.beq c t
        rw [← beq_add_right k (r + 1) c, H, Nat.add_comm (r + 1) c, Nat.add_right_comm t 1 r,
          beq_comm' c t]
        exact beq_add_right t c (r + 1)
      · show Nat.beq k r = Nat.beq c (t + 1)
        rw [← beq_add_right k r c, H, Nat.add_comm r c, beq_comm' c (t + 1)]
        exact beq_add_right (t + 1) c r

theorem covers_bool_flip : ∀ a b x1 x2 e1 y1 y2 e2 : Bool,
    (cond a x2 x1 && (cond a x1 x2 && (cond b y2 y1 && (cond b y1 y2 && !(e1 && e2))))) =
      (x1 && (x2 && (y1 && (y2 && !(e1 && e2))))) := by
  decide

theorem covers_bool_swap : ∀ a b x1 x2 e1 y1 y2 e2 : Bool,
    (cond a y2 y1 && (cond a y1 y2 && (cond b x2 x1 && (cond b x1 x2 && !(e2 && e1))))) =
      (x1 && (x2 && (y1 && (y2 && !(e1 && e2))))) := by
  decide

/-- **Covering is equivariant.** For a tromino on the board and a board cell,
    `g · t` covers `g · c` exactly when `t` covers `c`. -/
theorem covers_actT (n : Nat) (g : Sym) (t : Tromino) (ht : Inside n t)
    (cx cy : Nat) (hx : cx < 2 ^ n) (hy : cy < 2 ^ n) :
    covers (actT n g t) (actB n g cx cy).1 (actB n g cx cy).2 = covers t cx cy := by
  obtain ⟨s, a, b⟩ := g
  obtain ⟨tx, ty, mx, my⟩ := t
  obtain ⟨htx, hty⟩ := ht
  cases s
  · obtain ⟨X1, X2, X3⟩ := cov_axis (2 ^ n) tx cx mx a htx hx
    obtain ⟨Y1, Y2, Y3⟩ := cov_axis (2 ^ n) ty cy my b hty hy
    show (Nat.ble (flipAt (2 ^ n - 1) a tx) (flipAt (2 ^ n) a cx) &&
      (Nat.ble (flipAt (2 ^ n) a cx) (flipAt (2 ^ n - 1) a tx + 1) &&
      (Nat.ble (flipAt (2 ^ n - 1) b ty) (flipAt (2 ^ n) b cy) &&
      (Nat.ble (flipAt (2 ^ n) b cy) (flipAt (2 ^ n - 1) b ty + 1) &&
      !(Nat.beq (flipAt (2 ^ n) a cx) (flipAt (2 ^ n - 1) a tx + b2n (mx ^^ a)) &&
        Nat.beq (flipAt (2 ^ n) b cy) (flipAt (2 ^ n - 1) b ty + b2n (my ^^ b))))))) =
      covers ⟨tx, ty, (mx, my)⟩ cx cy
    rw [X1, X2, X3, Y1, Y2, Y3]
    exact covers_bool_flip a b _ _ _ _ _ _
  · obtain ⟨X1, X2, X3⟩ := cov_axis (2 ^ n) tx cx mx b htx hx
    obtain ⟨Y1, Y2, Y3⟩ := cov_axis (2 ^ n) ty cy my a hty hy
    show (Nat.ble (flipAt (2 ^ n - 1) a ty) (flipAt (2 ^ n) a cy) &&
      (Nat.ble (flipAt (2 ^ n) a cy) (flipAt (2 ^ n - 1) a ty + 1) &&
      (Nat.ble (flipAt (2 ^ n - 1) b tx) (flipAt (2 ^ n) b cx) &&
      (Nat.ble (flipAt (2 ^ n) b cx) (flipAt (2 ^ n - 1) b tx + 1) &&
      !(Nat.beq (flipAt (2 ^ n) a cy) (flipAt (2 ^ n - 1) a ty + b2n (my ^^ a)) &&
        Nat.beq (flipAt (2 ^ n) b cx) (flipAt (2 ^ n - 1) b tx + b2n (mx ^^ b))))))) =
      covers ⟨tx, ty, (mx, my)⟩ cx cy
    rw [X1, X2, X3, Y1, Y2, Y3]
    exact covers_bool_swap a b _ _ _ _ _ _

/-! ## §16 Every tromino of the tiling lies on the board (no hypothesis on the hole) -/

theorem inside_shift {S u : Nat} (b : Bool) (hu : u + 2 ≤ S) : u + offS S b + 2 ≤ S + S := by
  cases b with
  | false => exact Nat.le_trans hu (Nat.le_add_right S S)
  | true =>
    show u + S + 2 ≤ S + S
    rw [Nat.add_right_comm u S 2]
    exact Nat.add_le_add_right hu S

theorem bridge_inside (p : Nat) : p + 1 - 1 + 2 ≤ p + 1 + (p + 1) :=
  Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le p)) (p + 1)

theorem tile_inside (n : Nat) : ∀ hx hy : Nat, ∀ t ∈ tile n hx hy, Inside n t := by
  induction n with
  | zero => intro hx hy t ht; exact nomatch ht
  | succ n ih =>
    intro hx hy t ht
    obtain ⟨p, hp⟩ := two_pow_succ_form n
    cases mem_cons_inv ht with
    | inl e =>
      subst e
      show 2 ^ n - 1 + 2 ≤ 2 ^ (n + 1) ∧ 2 ^ n - 1 + 2 ≤ 2 ^ (n + 1)
      rw [two_pow_succ_eq, hp]
      exact ⟨bridge_inside p, bridge_inside p⟩
    | inr h =>
      obtain ⟨q, hq⟩ := mem_concat4 h
      obtain ⟨u, hu, rfl⟩ := mem_map_inv hq
      obtain ⟨h1, h2⟩ := ih _ _ u hu
      show u.x + offS (2 ^ n) q.1 + 2 ≤ 2 ^ (n + 1) ∧ u.y + offS (2 ^ n) q.2 + 2 ≤ 2 ^ (n + 1)
      rw [two_pow_succ_eq]
      exact ⟨inside_shift q.1 h1, inside_shift q.2 h2⟩

/-! ## §17 The four structural facts of the recursion -/

/-- The quadrant of the transformed hole is the transformed quadrant (Base `act`). -/
theorem quadrant_actB (n : Nat) (g : Sym) (hx hy : Nat) :
    quadS (2 ^ n) (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2 =
      act g (quadS (2 ^ n) hx hy) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  obtain ⟨s, a, b⟩ := g
  cases s
  · show (Nat.ble (2 ^ n) (flipAt (2 ^ (n + 1)) a hx), Nat.ble (2 ^ n) (flipAt (2 ^ (n + 1)) b hy)) =
      (Nat.ble (2 ^ n) hx ^^ a, Nat.ble (2 ^ n) hy ^^ b)
    rw [two_pow_succ_eq, hp, ble_flip_board, ble_flip_board]
  · show (Nat.ble (2 ^ n) (flipAt (2 ^ (n + 1)) a hy), Nat.ble (2 ^ n) (flipAt (2 ^ (n + 1)) b hx)) =
      (Nat.ble (2 ^ n) hy ^^ a, Nat.ble (2 ^ n) hx ^^ b)
    rw [two_pow_succ_eq, hp, ble_flip_board, ble_flip_board]

/-- The bridge is carried to the bridge of the transformed deficient quadrant. -/
theorem bridge_actT (n : Nat) (g : Sym) (qm : Cell) :
    actT (n + 1) g (bridgeS (2 ^ n) qm) = bridgeS (2 ^ n) (act g qm) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  obtain ⟨s, a, b⟩ := g
  cases s
  · show (⟨flipAt (2 ^ (n + 1) - 1) a (2 ^ n - 1), flipAt (2 ^ (n + 1) - 1) b (2 ^ n - 1),
        act ⟨false, a, b⟩ qm⟩ : Tromino) = ⟨2 ^ n - 1, 2 ^ n - 1, act ⟨false, a, b⟩ qm⟩
    rw [two_pow_succ_eq, hp]
    show (⟨flipAt (p + 1 + (p + 1) - 1) a p, flipAt (p + 1 + (p + 1) - 1) b p,
        act ⟨false, a, b⟩ qm⟩ : Tromino) = ⟨p, p, act ⟨false, a, b⟩ qm⟩
    rw [flip_center, flip_center]
  · show (⟨flipAt (2 ^ (n + 1) - 1) a (2 ^ n - 1), flipAt (2 ^ (n + 1) - 1) b (2 ^ n - 1),
        act ⟨true, a, b⟩ qm⟩ : Tromino) = ⟨2 ^ n - 1, 2 ^ n - 1, act ⟨true, a, b⟩ qm⟩
    rw [two_pow_succ_eq, hp]
    show (⟨flipAt (p + 1 + (p + 1) - 1) a p, flipAt (p + 1 + (p + 1) - 1) b p,
        act ⟨true, a, b⟩ qm⟩ : Tromino) = ⟨p, p, act ⟨true, a, b⟩ qm⟩
    rw [flip_center, flip_center]

/-- A tromino placed in quadrant `q` and then transformed at scale `n+1` equals
    the tromino transformed at scale `n` and placed in quadrant `g · q`. -/
theorem shift_actT (n : Nat) (g : Sym) (q : Cell) (t : Tromino) (ht : Inside n t) :
    actT (n + 1) g (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2) t) =
      shift (offS (2 ^ n) (act g q).1) (offS (2 ^ n) (act g q).2) (actT n g t) := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  obtain ⟨s, a, b⟩ := g
  obtain ⟨qx, qy⟩ := q
  obtain ⟨tx, ty, m⟩ := t
  obtain ⟨htx, hty⟩ := ht
  rw [hp] at htx hty
  cases s
  · show (⟨flipAt (2 ^ (n + 1) - 1) a (tx + offS (2 ^ n) qx),
        flipAt (2 ^ (n + 1) - 1) b (ty + offS (2 ^ n) qy), act ⟨false, a, b⟩ m⟩ : Tromino) =
      ⟨flipAt (2 ^ n - 1) a tx + offS (2 ^ n) (qx ^^ a),
        flipAt (2 ^ n - 1) b ty + offS (2 ^ n) (qy ^^ b), act ⟨false, a, b⟩ m⟩
    rw [two_pow_succ_eq, hp, flip_shift p tx qx a htx, flip_shift p ty qy b hty]
  · show (⟨flipAt (2 ^ (n + 1) - 1) a (ty + offS (2 ^ n) qy),
        flipAt (2 ^ (n + 1) - 1) b (tx + offS (2 ^ n) qx), act ⟨true, a, b⟩ m⟩ : Tromino) =
      ⟨flipAt (2 ^ n - 1) a ty + offS (2 ^ n) (qy ^^ a),
        flipAt (2 ^ n - 1) b tx + offS (2 ^ n) (qx ^^ b), act ⟨true, a, b⟩ m⟩
    rw [two_pow_succ_eq, hp, flip_shift p ty qy a hty, flip_shift p tx qx b htx]

/-- Cell equality is preserved by every symmetry. -/
theorem cellEq_act : ∀ s a b px py qx qy : Bool,
    cellEq (act ⟨s, a, b⟩ (px, py)) (act ⟨s, a, b⟩ (qx, qy)) = cellEq (px, py) (qx, qy) := by
  decide

theorem cellEq_act' (g : Sym) (c d : Cell) : cellEq (act g c) (act g d) = cellEq c d := by
  obtain ⟨s, a, b⟩ := g
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  exact cellEq_act s a b c1 c2 d1 d2

theorem cellEq_true : ∀ x1 x2 y1 y2 : Bool, cellEq (x1, x2) (y1, y2) = true → x1 = y1 ∧ x2 = y2 := by
  decide

theorem subHole_true {S : Nat} {qm q : Cell} {hx hy : Nat} (h : cellEq q qm = true) :
    subHoleS S qm q hx hy = (hx - offS S q.1, hy - offS S q.2) := by
  show cond (cellEq q qm) _ _ = _
  rw [h]
  rfl

theorem subHole_false {S : Nat} {qm q : Cell} {hx hy : Nat} (h : cellEq q qm = false) :
    subHoleS S qm q hx hy = (cond q.1 0 (S - 1), cond q.2 0 (S - 1)) := by
  show cond (cellEq q qm) _ _ = _
  rw [h]
  rfl

/-- The sub-hole handed to quadrant `g · q` of the transformed board is the
    transformed sub-hole of quadrant `q`. -/
theorem subHole_actB (n : Nat) (g : Sym) (q : Cell) (hx hy : Nat) :
    subHoleS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) (act g q)
        (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2 =
      actB n g (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).1
        (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).2 := by
  obtain ⟨p, hp⟩ := two_pow_succ_form n
  cases hc : cellEq q (quadS (2 ^ n) hx hy) with
  | false =>
    rw [subHole_false ((cellEq_act' g q _).trans hc), subHole_false hc]
    obtain ⟨s, a, b⟩ := g
    obtain ⟨q1, q2⟩ := q
    cases s
    · show (cond (q1 ^^ a) 0 (2 ^ n - 1), cond (q2 ^^ b) 0 (2 ^ n - 1)) =
        (flipAt (2 ^ n) a (cond q1 0 (2 ^ n - 1)), flipAt (2 ^ n) b (cond q2 0 (2 ^ n - 1)))
      rw [hp]
      show (cond (q1 ^^ a) 0 p, cond (q2 ^^ b) 0 p) =
        (flipAt (p + 1) a (cond q1 0 p), flipAt (p + 1) b (cond q2 0 p))
      rw [flip_centre_coord, flip_centre_coord]
    · show (cond (q2 ^^ a) 0 (2 ^ n - 1), cond (q1 ^^ b) 0 (2 ^ n - 1)) =
        (flipAt (2 ^ n) a (cond q2 0 (2 ^ n - 1)), flipAt (2 ^ n) b (cond q1 0 (2 ^ n - 1)))
      rw [hp]
      show (cond (q2 ^^ a) 0 p, cond (q1 ^^ b) 0 p) =
        (flipAt (p + 1) a (cond q2 0 p), flipAt (p + 1) b (cond q1 0 p))
      rw [flip_centre_coord, flip_centre_coord]
  | true =>
    rw [subHole_true ((cellEq_act' g q _).trans hc), subHole_true hc]
    obtain ⟨s, a, b⟩ := g
    obtain ⟨q1, q2⟩ := q
    obtain ⟨rfl, rfl⟩ := cellEq_true _ _ _ _ hc
    cases s
    · show (flipAt (2 ^ (n + 1)) a hx - offS (2 ^ n) (Nat.ble (2 ^ n) hx ^^ a),
          flipAt (2 ^ (n + 1)) b hy - offS (2 ^ n) (Nat.ble (2 ^ n) hy ^^ b)) =
        (flipAt (2 ^ n) a (hx - offS (2 ^ n) (Nat.ble (2 ^ n) hx)),
          flipAt (2 ^ n) b (hy - offS (2 ^ n) (Nat.ble (2 ^ n) hy)))
      rw [two_pow_succ_eq, hp, sub_flip, sub_flip]
    · show (flipAt (2 ^ (n + 1)) a hy - offS (2 ^ n) (Nat.ble (2 ^ n) hy ^^ a),
          flipAt (2 ^ (n + 1)) b hx - offS (2 ^ n) (Nat.ble (2 ^ n) hx ^^ b)) =
        (flipAt (2 ^ n) a (hy - offS (2 ^ n) (Nat.ble (2 ^ n) hy)),
          flipAt (2 ^ n) b (hx - offS (2 ^ n) (Nat.ble (2 ^ n) hx)))
      rw [two_pow_succ_eq, hp, sub_flip, sub_flip]

/-! ## §18 Relabelling the four quadrants is a permutation of the listing -/

/-- Exchange the first two of four blocks. -/
theorem sw1 {α : Type} (w x y z : List α) : (w ++ x ++ y ++ z).Perm (x ++ w ++ y ++ z) :=
  ((perm_append_comm' w x).append_right y).append_right z

/-- Exchange the middle two of four blocks. -/
theorem sw2 {α : Type} (w x y z : List α) : (w ++ x ++ y ++ z).Perm (w ++ y ++ x ++ z) := by
  have h : (w ++ x ++ y).Perm (w ++ y ++ x) := by
    rw [append_assoc' w x y, append_assoc' w y x]
    exact (perm_append_comm' x y).append_left w
  exact h.append_right z

/-- Exchange the last two of four blocks. -/
theorem sw3 {α : Type} (w x y z : List α) : (w ++ x ++ y ++ z).Perm (w ++ x ++ z ++ y) := by
  rw [append_assoc' (w ++ x) y z, append_assoc' (w ++ x) z y]
  exact (perm_append_comm' y z).append_left _

theorem concat4_act_perm {α : Type} [DecidableEq α] (F : Cell → List α) (g : Sym) :
    (concat4 (fun q => F (act g q))).Perm (concat4 F) := by
  obtain ⟨s, a, b⟩ := g
  cases s <;> cases a <;> cases b
  · exact List.Perm.refl _
  · exact (sw1 _ _ _ _).trans (sw3 _ _ _ _)
  · exact (sw2 _ _ _ _).trans ((sw1 _ _ _ _).trans ((sw3 _ _ _ _).trans (sw2 _ _ _ _)))
  · exact (sw1 _ _ _ _).trans ((sw2 _ _ _ _).trans ((sw3 _ _ _ _).trans
      ((sw1 _ _ _ _).trans ((sw2 _ _ _ _).trans (sw1 _ _ _ _)))))
  · exact sw2 _ _ _ _
  · exact (sw2 _ _ _ _).trans ((sw1 _ _ _ _).trans (sw3 _ _ _ _))
  · exact (sw1 _ _ _ _).trans ((sw3 _ _ _ _).trans (sw2 _ _ _ _))
  · exact (sw1 _ _ _ _).trans ((sw2 _ _ _ _).trans ((sw3 _ _ _ _).trans
      ((sw2 _ _ _ _).trans (sw1 _ _ _ _))))

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
    have hR : (tile (n + 1) hx hy).map (actT (n + 1) g) =
        bridgeS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) ::
          concat4 (fun q =>
            ((tile n (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).1
                (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).2).map
              (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2))).map (actT (n + 1) g)) := by
      show actT (n + 1) g (bridgeS (2 ^ n) (quadS (2 ^ n) hx hy)) ::
          (concat4 (fun q =>
            (tile n (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).1
                (subHoleS (2 ^ n) (quadS (2 ^ n) hx hy) q hx hy).2).map
              (shift (offS (2 ^ n) q.1) (offS (2 ^ n) q.2)))).map (actT (n + 1) g) = _
      rw [bridge_actT, map_concat4]
    have hL : tile (n + 1) (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2 =
        bridgeS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) ::
          concat4 (fun q' =>
            (tile n (subHoleS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) q'
                (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2).1
              (subHoleS (2 ^ n) (act g (quadS (2 ^ n) hx hy)) q'
                (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2).2).map
              (shift (offS (2 ^ n) q'.1) (offS (2 ^ n) q'.2))) := by
      show bridgeS (2 ^ n) (quadS (2 ^ n) (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2) ::
          concat4 (fun q' =>
            (tile n (subHoleS (2 ^ n) (quadS (2 ^ n) (actB (n + 1) g hx hy).1
                  (actB (n + 1) g hx hy).2) q' (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2).1
              (subHoleS (2 ^ n) (quadS (2 ^ n) (actB (n + 1) g hx hy).1
                  (actB (n + 1) g hx hy).2) q' (actB (n + 1) g hx hy).1 (actB (n + 1) g hx hy).2).2).map
              (shift (offS (2 ^ n) q'.1) (offS (2 ^ n) q'.2))) = _
      rw [quadrant_actB]
    rw [hL, hR]
    refine List.Perm.cons _ ?_
    refine List.Perm.trans (concat4_act_perm _ g).symm (concat4_perm fun q => ?_)
    -- quadrant g·q of the new board against quadrant q of the old one
    rw [subHole_actB]
    refine (perm_map' _ (ih g _ _)).trans (List.Perm.of_eq ?_)
    exact (map_map' _ _ _).trans ((map_congr' fun t ht =>
      (shift_actT n g q t (tile_inside n _ _ t ht)).symm).trans (map_map' _ _ _).symm)

/-! ## §20 Consequences and non-vacuity -/

/-- Coverage counts do not depend on the order of the list. -/
theorem cov_perm {T U : List Tromino} (h : T.Perm U) (cx cy : Nat) : cov T cx cy = cov U cx cy := by
  induction h with
  | nil => rfl
  | cons t _ ih => exact congrArg (cond (covers t cx cy) 1 0 + ·) ih
  | swap t u T => exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem cov_map_actT (n : Nat) (g : Sym) (T : List Tromino) (hT : ∀ t ∈ T, Inside n t)
    (cx cy : Nat) (hx : cx < 2 ^ n) (hy : cy < 2 ^ n) :
    cov (T.map (actT n g)) (actB n g cx cy).1 (actB n g cx cy).2 = cov T cx cy := by
  induction T with
  | nil => rfl
  | cons t T ih =>
    show cond (covers (actT n g t) (actB n g cx cy).1 (actB n g cx cy).2) 1 0 +
        cov (T.map (actT n g)) (actB n g cx cy).1 (actB n g cx cy).2 =
      cond (covers t cx cy) 1 0 + cov T cx cy
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

