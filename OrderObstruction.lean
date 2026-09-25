/-
  OrderObstruction.lean — bare Lean 4, no Mathlib.
  Incommensurability blocks order-preserving maps back onto the rationals.
-/
namespace PrimitiveReflexivity.OrderObstruction

variable {Q K : Type} [LT Q] [LE Q] [LT K]

/-- Layer 1: any order-respecting retraction onto a dense embedded carrier
    is forced to be the identity. -/
theorem retraction_is_identity
    (ι : Q → K) (f : K → Q)
    (ι_lt : ∀ a b : Q, a < b ↔ ι a < ι b)
    (trichK : ∀ x y : K, x < y ∨ x = y ∨ y < x)
    (dense : ∀ x y : K, x < y → ∃ q : Q, x < ι q ∧ ι q < y)
    (Q_lt_not_le : ∀ a b : Q, a < b → ¬ b ≤ a)
    (mono : ∀ x y : K, x < y → f x ≤ f y)
    (retract : ∀ q : Q, f (ι q) = q) :
    ∀ x : K, ι (f x) = x := by
  intro x
  rcases trichK (ι (f x)) x with h | h | h
  · obtain ⟨q, h1, h2⟩ := dense _ _ h
    have hle : q ≤ f x := by have := mono _ _ h2; rwa [retract] at this
    exact absurd hle (Q_lt_not_le _ _ ((ι_lt _ _).mpr h1))
  · exact h
  · obtain ⟨q, h1, h2⟩ := dense _ _ h
    have hle : f x ≤ q := by have := mono _ _ h1; rwa [retract] at this
    exact absurd hle (Q_lt_not_le _ _ ((ι_lt _ _).mpr h2))

/-- Corollary: if some point of K is not hit by ι, no such retraction exists. -/
theorem no_retraction_if_gap
    (ι : Q → K)
    (ι_lt : ∀ a b : Q, a < b ↔ ι a < ι b)
    (trichK : ∀ x y : K, x < y ∨ x = y ∨ y < x)
    (dense : ∀ x y : K, x < y → ∃ q : Q, x < ι q ∧ ι q < y)
    (Q_lt_not_le : ∀ a b : Q, a < b → ¬ b ≤ a)
    (gap : ∃ x : K, ∀ q : Q, ι q ≠ x) :
    ¬ ∃ f : K → Q, (∀ x y, x < y → f x ≤ f y) ∧ (∀ q, f (ι q) = q) := by
  rintro ⟨f, mono, retract⟩
  obtain ⟨x, hx⟩ := gap
  exact hx (f x) (retraction_is_identity ι f ι_lt trichK dense Q_lt_not_le mono retract x)

/-- Layer 2: descent. No natural numbers with p² = 2q², q ≠ 0. -/
theorem sq_odd_of_odd (p : Nat) (h : p % 2 = 1) : (p * p) % 2 = 1 := by
  rw [Nat.mul_mod, h]

theorem no_sqrt_two_nat : ∀ p q : Nat, q ≠ 0 → p * p ≠ 2 * (q * q) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro q hq heq
    have hp_even : p % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one p with h | h
      · exact h
      · have := sq_odd_of_odd p h; rw [heq] at this; omega
    obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k := ⟨p / 2, by omega⟩
    have h4 : 2 * k * (2 * k) = 2 * (2 * (k * k)) := by
      rw [Nat.mul_mul_mul_comm, Nat.mul_assoc]
    have hqk : q * q = 2 * (k * k) := by
      rw [h4] at heq; exact (Nat.eq_of_mul_eq_mul_left (by decide) heq).symm
    have hk0 : k ≠ 0 := by
      intro hk; subst hk
      have : q * q = 0 := by simpa using hqk
      rcases Nat.mul_eq_zero.mp this with h | h <;> exact hq h
    have hkk : 0 < k * k := Nat.mul_pos (Nat.pos_of_ne_zero hk0) (Nat.pos_of_ne_zero hk0)
    have hlt : q < 2 * k := by
      apply Nat.lt_of_not_le; intro hle
      have := Nat.mul_le_mul hle hle
      rw [h4, ← hqk] at this
      omega
    exact ih q hlt k hk0 hqk

/-- Layer 3: the main theorem. If K contains an element s with s·s = 2 and
    Q has no square root of 2, then no order-preserving map K → Q fixes Q. -/
theorem no_order_retraction_of_sqrt_two [Mul Q] [Mul K]
    (two : Q) (ι : Q → K)
    (ι_mul : ∀ a b : Q, ι (a * b) = ι a * ι b)
    (ι_inj : ∀ a b : Q, ι a = ι b → a = b)
    (ι_lt : ∀ a b : Q, a < b ↔ ι a < ι b)
    (trichK : ∀ x y : K, x < y ∨ x = y ∨ y < x)
    (dense : ∀ x y : K, x < y → ∃ q : Q, x < ι q ∧ ι q < y)
    (Q_lt_not_le : ∀ a b : Q, a < b → ¬ b ≤ a)
    (s : K) (hs : s * s = ι two)
    (no_rat_sqrt_two : ∀ r : Q, r * r ≠ two) :
    ¬ ∃ f : K → Q, (∀ x y, x < y → f x ≤ f y) ∧ (∀ q, f (ι q) = q) := by
  apply no_retraction_if_gap ι ι_lt trichK dense Q_lt_not_le
  refine ⟨s, fun r hr => no_rat_sqrt_two r (ι_inj _ _ ?_)⟩
  rw [ι_mul, hr, hs]


/-! ## Audit step 3: discharge the √2 hypothesis for core `Rat`. -/
theorem sqr_num (r : Rat) : (r * r).num = r.num * r.num ∧ (r * r).den = r.den * r.den := by
  have hc : (r.num * r.num).natAbs.Coprime (r.den * r.den) := by
    rw [Int.natAbs_mul]
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_left r.reduced r.reduced) (Nat.Coprime.mul_left r.reduced r.reduced)
  rw [Rat.num_mul, Rat.den_mul, hc.gcd_eq_one]
  simp

theorem rat_sq_eq_two_nat (r : Rat) (h : r * r = 2) :
    r.num.natAbs * r.num.natAbs = 2 * (r.den * r.den) := by
  have e := Rat.eq_iff_mul_eq_mul.mp h
  obtain ⟨hn, hd⟩ := sqr_num r
  rw [hn, hd] at e
  simp at e
  have := congrArg Int.natAbs e
  rw [Int.natAbs_mul, Int.natAbs_mul] at this
  rw [Int.natAbs_mul] at this; simpa using this

theorem rat_no_sqrt_two : ∀ r : Rat, r * r ≠ 2 := by
  intro r h
  exact no_sqrt_two_nat _ _ r.den_nz (rat_sq_eq_two_nat r h)

/-! ## Audit step 1: satisfiability witness. All hypotheses of
    `retraction_is_identity` hold simultaneously for Q = K = Rat, ι = f = id,
    so the theorem is not vacuous. -/
theorem rat_trich (x y : Rat) : x < y ∨ x = y ∨ y < x := by
  rcases Rat.le_total (a := x) (b := y) with h | h
  · rcases Rat.le_iff_lt_or_eq.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases Rat.le_iff_lt_or_eq.mp h with h' | h'
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl h'.symm)

theorem two_mul_eq (x : Rat) : x * 2 = x + x := by grind

theorem rat_dense (x y : Rat) (h : x < y) : ∃ q : Rat, x < q ∧ q < y := by
  have h2 : (0 : Rat) < 2 := by decide
  refine ⟨(x + y) / 2, ?_, ?_⟩
  · rw [Rat.lt_div_iff h2, two_mul_eq]; exact Rat.add_lt_add_left.mpr h
  · rw [Rat.div_lt_iff h2, two_mul_eq]; exact Rat.add_lt_add_right.mpr h

theorem witness_rat :
    ∀ x : Rat, id (id x) = x :=
  retraction_is_identity (Q := Rat) (K := Rat) id id
    (fun _ _ => Iff.rfl) rat_trich rat_dense
    (fun _ _ h => Rat.not_le.mpr h)
    (fun _ _ h => Rat.le_of_lt h) (fun _ => rfl)

/-! ## Audit step 2: necessity tests. Dropping a hypothesis breaks the conclusion. -/

/-- Density is needed: Q = K = Nat, ι q = 2q, f x = x/2 satisfies every other
    hypothesis, density fails, and the conclusion fails at x = 1. -/
theorem density_needed :
    (∀ a b : Nat, a < b ↔ 2 * a < 2 * b) ∧
    (∀ x y : Nat, x < y ∨ x = y ∨ y < x) ∧
    (∀ a b : Nat, a < b → ¬ b ≤ a) ∧
    (∀ x y : Nat, x < y → x / 2 ≤ y / 2) ∧
    (∀ q : Nat, 2 * q / 2 = q) ∧
    ¬ (∀ x y : Nat, x < y → ∃ q, x < 2 * q ∧ 2 * q < y) ∧
    ¬ (∀ x : Nat, 2 * (x / 2) = x) := by
  refine ⟨fun _ _ => by omega, fun _ _ => by omega, fun _ _ => by omega,
    fun _ _ _ => by omega, fun _ => by omega, ?_, ?_⟩
  · intro h; obtain ⟨q, h1, h2⟩ := h 0 1 (by decide); omega
  · intro h; have := h 1; omega

/-- The retraction condition is needed: the constant map 0 on Rat is
    monotone but not the identity. -/
theorem retract_needed :
    (∀ x y : Rat, x < y → (fun _ => (0 : Rat)) x ≤ (fun _ => (0 : Rat)) y) ∧
    ¬ (∀ x : Rat, (fun _ => (0 : Rat)) x = x) := by
  refine ⟨fun _ _ _ => Rat.le_refl, ?_⟩
  intro h; have := h 1; exact absurd this (by decide)

/-- Main theorem specialized to Rat, with nothing load-bearing assumed about √2. -/
theorem no_order_retraction_rat {K : Type} [LT K] [Mul K]
    (ι : Rat → K)
    (ι_mul : ∀ a b, ι (a * b) = ι a * ι b)
    (ι_inj : ∀ a b, ι a = ι b → a = b)
    (ι_lt : ∀ a b, a < b ↔ ι a < ι b)
    (trichK : ∀ x y : K, x < y ∨ x = y ∨ y < x)
    (dense : ∀ x y : K, x < y → ∃ q, x < ι q ∧ ι q < y)
    (s : K) (hs : s * s = ι 2) :
    ¬ ∃ f : K → Rat, (∀ x y, x < y → f x ≤ f y) ∧ (∀ q, f (ι q) = q) :=
  no_order_retraction_of_sqrt_two 2 ι ι_mul ι_inj ι_lt trichK dense
    (fun _ _ h => Rat.not_le.mpr h) s hs rat_no_sqrt_two

/-! ## Localized obstruction: density and trichotomy needed only at the gap point. -/
theorem no_retraction_local {Q K : Type} [LT Q] [LE Q] [LT K]
    (ι : Q → K)
    (ι_lt : ∀ a b : Q, a < b ↔ ι a < ι b)
    (Q_lt_not_le : ∀ a b : Q, a < b → ¬ b ≤ a)
    (s : K)
    (trich_s : ∀ q : Q, ι q < s ∨ s < ι q)
    (below : ∀ q : Q, ι q < s → ∃ p : Q, ι q < ι p ∧ ι p < s)
    (above : ∀ q : Q, s < ι q → ∃ p : Q, s < ι p ∧ ι p < ι q) :
    ¬ ∃ f : K → Q, (∀ x y, x < y → f x ≤ f y) ∧ (∀ q, f (ι q) = q) := by
  rintro ⟨f, mono, retract⟩
  rcases trich_s (f s) with h | h
  · obtain ⟨p, h1, h2⟩ := below _ h
    have : p ≤ f s := by have := mono _ _ h2; rwa [retract] at this
    exact Q_lt_not_le _ _ ((ι_lt _ _).mpr h1) this
  · obtain ⟨p, h1, h2⟩ := above _ h
    have : f s ≤ p := by have := mono _ _ h1; rwa [retract] at this
    exact Q_lt_not_le _ _ ((ι_lt _ _).mpr h2) this

/-! ## Concrete model: ℚ(√2) as pairs a + b√2 (Corollary 1.3). -/
structure QS where
  a : Rat
  b : Rat

namespace QS

/-- Field multiplication: (a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2. -/
instance : Mul QS := ⟨fun x y => ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩⟩

/-- Positivity of a + b√2, decided by signs and the norm a² − 2b². -/
def Pos (x : QS) : Prop :=
  (0 ≤ x.a ∧ 0 ≤ x.b ∧ (0 < x.a ∨ 0 < x.b)) ∨
  (0 ≤ x.a ∧ x.b < 0 ∧ 2 * (x.b * x.b) < x.a * x.a) ∨
  (x.a < 0 ∧ 0 ≤ x.b ∧ x.a * x.a < 2 * (x.b * x.b))

instance : LT QS := ⟨fun x y => Pos ⟨y.a - x.a, y.b - x.b⟩⟩

/-- Embedding of the rationals: q ↦ q + 0√2. -/
def emb (q : Rat) : QS := ⟨q, 0⟩
/-- The gap point √2 = 0 + 1√2. -/
def s : QS := ⟨0, 1⟩

theorem sq_nonneg (c : Rat) : 0 ≤ c * c := by
  rcases Rat.le_total (a := 0) (b := c) with h | h
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -c := by grind
    have := Rat.mul_nonneg h' h'
    grind

theorem s_mul_s : s * s = emb 2 := by
  show (⟨0 * 0 + 2 * (1 * 1), 0 * 1 + 1 * 0⟩ : QS) = ⟨2, 0⟩
  congr 1 <;> grind

theorem emb_mul (x y : Rat) : emb (x * y) = emb x * emb y := by
  show (⟨x * y, 0⟩ : QS) = ⟨x * y + 2 * (0 * 0), x * 0 + 0 * y⟩
  congr 1 <;> grind

theorem emb_inj (x y : Rat) (h : emb x = emb y) : x = y := by
  cases h; rfl

theorem emb_lt (x y : Rat) : x < y ↔ emb x < emb y := by
  show x < y ↔ Pos ⟨y - x, 0 - 0⟩
  unfold Pos
  have := sq_nonneg (y - x)
  constructor
  · intro h; left; refine ⟨?_, ?_, ?_⟩ <;> grind
  · intro h; rcases h with h | h | h <;> grind

theorem emb_lt_s (q : Rat) : emb q < s ↔ (q ≤ 0 ∨ q * q < 2) := by
  show Pos ⟨0 - q, 1 - 0⟩ ↔ _
  unfold Pos
  constructor
  · intro h; rcases h with h | h | h <;> grind
  · intro h
    rcases Rat.le_total (a := q) (b := 0) with hq | hq
    · left; refine ⟨?_, ?_, ?_⟩ <;> grind
    · rcases h with h | h
      · left; refine ⟨?_, ?_, ?_⟩ <;> grind
      · rcases Rat.le_iff_lt_or_eq.mp hq with hq | hq
        · right; right; refine ⟨?_, ?_, ?_⟩ <;> grind
        · left; refine ⟨?_, ?_, ?_⟩ <;> grind

theorem s_lt_emb (q : Rat) : s < emb q ↔ (0 ≤ q ∧ 2 < q * q) := by
  show Pos ⟨q - 0, 0 - 1⟩ ↔ _
  unfold Pos
  constructor
  · intro h; rcases h with h | h | h <;> grind
  · intro h; right; left; refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Trichotomy at √2: every rational is strictly below or above it.
    The tie case is excluded by the irrationality of √2 (Proposition 1.1). -/
theorem trich_s (q : Rat) : emb q < s ∨ s < emb q := by
  rw [emb_lt_s, s_lt_emb]
  rcases Rat.le_total (a := q) (b := 0) with hq | hq
  · exact Or.inl (Or.inl hq)
  · rcases rat_trich (q * q) 2 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact absurd h (rat_no_sqrt_two q)
    · exact Or.inr ⟨hq, h⟩

/-- The side-and-diagonal step r ↦ (2r + 2)/(r + 2).

    Correction: starting from 1, the iterates 1, 4/3, 7/5, 24/17, 41/29, …
    do NOT all sit in the classical side-and-diagonal sequence. Only every
    other term does (7/5, 41/29, …, the terms `step_below`/`step_above`
    reach from an odd number of steps); the intermediate terms are the
    hyperbolic reflections of those side-and-diagonal terms across √2 under
    x ↦ 2/x (4/3 = 2/(3/2), 24/17 = 2/(17/12)). An earlier informal
    description treating every iterate as a side-and-diagonal number is
    corrected here. -/
def step (r : Rat) : Rat := (2 * r + 2) / (r + 2)

theorem step_mul (r : Rat) (hr : 0 ≤ r) : step r * (r + 2) = 2 * r + 2 :=
  Rat.div_mul_cancel (by grind)

/-- Below √2, the step moves up and stays below. This lemma only certifies
    monotone approach from below; the sequence of iterates it drives
    alternates between side-and-diagonal terms and their x ↦ 2/x reflections
    — see the correction on `step`. -/
theorem step_below (r : Rat) (h0 : 0 < r) (h : r * r < 2) :
    r < step r ∧ step r * step r < 2 := by
  have hm := step_mul r (Rat.le_of_lt h0)
  have hpos : (0 : Rat) < (r + 2) * (r + 2) := Rat.mul_pos (by grind) (by grind)
  constructor
  · rw [step, Rat.lt_div_iff (by grind)]; grind
  · apply Rat.lt_of_mul_lt_mul_right (c := (r + 2) * (r + 2)) _ (Rat.le_of_lt hpos)
    have e : step r * step r * ((r + 2) * (r + 2)) = (2 * r + 2) * (2 * r + 2) := by grind
    rw [e]; grind

/-- Above √2, the step moves down and stays above. See the correction on
    `step` for what the resulting iterates actually are. -/
theorem step_above (r : Rat) (h0 : 0 ≤ r) (h : 2 < r * r) :
    step r < r ∧ 0 ≤ step r ∧ 2 < step r * step r := by
  have hm := step_mul r h0
  have hpos : (0 : Rat) < (r + 2) * (r + 2) := Rat.mul_pos (by grind) (by grind)
  refine ⟨?_, ?_, ?_⟩
  · rw [step, Rat.div_lt_iff (by grind)]; grind
  · rcases Rat.le_total (a := 0) (b := step r) with h1 | h1
    · exact h1
    · have : step r * (r + 2) ≤ 0 := by
        have := Rat.mul_nonneg (a := -step r) (b := r + 2) (by grind) (by grind); grind
      grind
  · apply Rat.lt_of_mul_lt_mul_right (c := (r + 2) * (r + 2)) _ (Rat.le_of_lt hpos)
    have e : step r * step r * ((r + 2) * (r + 2)) = (2 * r + 2) * (2 * r + 2) := by grind
    rw [e]; grind

theorem below_s (q : Rat) (h : emb q < s) : ∃ p, emb q < emb p ∧ emb p < s := by
  rw [emb_lt_s] at h
  rcases Rat.le_total (a := q) (b := 0) with hq | hq
  · refine ⟨1, (emb_lt _ _).mp (by grind), (emb_lt_s 1).mpr (Or.inr (by grind))⟩
  · rcases Rat.le_iff_lt_or_eq.mp hq with hq | hq
    · have h2 : q * q < 2 := by rcases h with h | h <;> grind
      obtain ⟨h3, h4⟩ := step_below q hq h2
      exact ⟨step q, (emb_lt _ _).mp h3, (emb_lt_s _).mpr (Or.inr h4)⟩
    · subst hq
      exact ⟨1, (emb_lt _ _).mp (by grind), (emb_lt_s 1).mpr (Or.inr (by grind))⟩

theorem above_s (q : Rat) (h : s < emb q) : ∃ p, s < emb p ∧ emb p < emb q := by
  rw [s_lt_emb] at h
  obtain ⟨h1, h2, h3⟩ := step_above q h.1 h.2
  exact ⟨step q, (s_lt_emb _).mpr ⟨h2, h3⟩, (emb_lt _ _).mp h1⟩

/-- MAIN WITNESS: in ℚ(√2), with √2 · √2 = 2 verified above, no order-preserving
    map back to ℚ can fix the rationals. -/
theorem no_order_retraction_Qsqrt2 :
    ¬ ∃ f : QS → Rat, (∀ x y, x < y → f x ≤ f y) ∧ (∀ q, f (emb q) = q) :=
  no_retraction_local emb emb_lt (fun _ _ h => Rat.not_le.mpr h) s trich_s below_s above_s

/-- Necessity of order-preservation: the projection a + b√2 ↦ a fixes every
    rational, yet it is not order-preserving (1 < √2 but 1 > 0). -/
theorem mono_needed :
    (∀ q, (fun x : QS => x.a) (emb q) = q) ∧
    ¬ (∀ x y : QS, x < y → (fun x : QS => x.a) x ≤ (fun x : QS => x.a) y) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro h
  have hlt : emb 1 < s := (emb_lt_s 1).mpr (Or.inr (by grind))
  have h10 : (1 : Rat) ≤ 0 := h _ _ hlt
  have h01 : ¬ ((1 : Rat) ≤ 0) := by grind
  exact h01 h10

/-! ## Roadmap Step 1: additive structure on QS (Section 9.3, "1. Additive structure"). -/

instance : Add QS := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg QS := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub QS := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Zero QS := ⟨⟨0, 0⟩⟩
instance : One QS := ⟨⟨1, 0⟩⟩

theorem add_assoc (x y z : QS) : (x + y) + z = x + (y + z) := by
  show (⟨x.a + y.a + z.a, x.b + y.b + z.b⟩ : QS) = ⟨x.a + (y.a + z.a), x.b + (y.b + z.b)⟩
  congr 1 <;> grind

theorem add_comm (x y : QS) : x + y = y + x := by
  show (⟨x.a + y.a, x.b + y.b⟩ : QS) = ⟨y.a + x.a, y.b + x.b⟩
  congr 1 <;> grind

theorem zero_add (x : QS) : (0 : QS) + x = x := by
  show (⟨0 + x.a, 0 + x.b⟩ : QS) = x
  congr 1 <;> grind

theorem add_zero (x : QS) : x + (0 : QS) = x := by
  show (⟨x.a + 0, x.b + 0⟩ : QS) = x
  congr 1 <;> grind

theorem add_left_neg (x : QS) : -x + x = (0 : QS) := by
  show (⟨-x.a + x.a, -x.b + x.b⟩ : QS) = ⟨0, 0⟩
  congr 1 <;> grind

theorem sub_eq_add_neg (x y : QS) : x - y = x + -y := by
  show (⟨x.a - y.a, x.b - y.b⟩ : QS) = ⟨x.a + -y.a, x.b + -y.b⟩
  congr 1 <;> grind

/-! ## Roadmap Step 2: Galois conjugate, norm, and multiplicative inverse
    (Section 9.3, "2. Inverse"). -/

/-- Galois conjugate a + b√2 ↦ a - b√2. -/
def conj (x : QS) : QS := ⟨x.a, -x.b⟩

/-- Norm a² − 2b², the rational part of x * conj x. -/
def norm (x : QS) : Rat := x.a * x.a - 2 * (x.b * x.b)

/-- The norm vanishes only at zero, discharged via `rat_no_sqrt_two`: a
    nonzero b with a² = 2b² would make a/b a rational square root of 2. -/
theorem norm_eq_zero_iff (x : QS) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hab : x.a * x.a = 2 * (x.b * x.b) := by
      have h0 : x.a * x.a - 2 * (x.b * x.b) = 0 := h
      grind
    by_cases hb : x.b = 0
    · have ha : x.a = 0 := by
        rw [hb] at hab
        grind [Rat.mul_eq_zero]
      show (⟨x.a, x.b⟩ : QS) = (⟨0, 0⟩ : QS)
      rw [ha, hb]
    · exfalso
      have hbb : x.b * x.b ≠ 0 := by
        intro hz
        rcases Rat.mul_eq_zero.mp hz with h' | h' <;> exact hb h'
      have hdiv : (x.a / x.b) * x.b = x.a := Rat.div_mul_cancel hb
      have e1 : (x.a / x.b) * (x.a / x.b) * (x.b * x.b) = 2 * (x.b * x.b) := by
        calc (x.a / x.b) * (x.a / x.b) * (x.b * x.b)
            = ((x.a / x.b) * x.b) * ((x.a / x.b) * x.b) := by grind
          _ = x.a * x.a := by rw [hdiv]
          _ = 2 * (x.b * x.b) := hab
      have hsq : (x.a / x.b) * (x.a / x.b) = 2 := by
        calc (x.a / x.b) * (x.a / x.b)
            = (x.a / x.b) * (x.a / x.b) * (x.b * x.b) / (x.b * x.b) :=
              (Rat.mul_div_cancel hbb).symm
          _ = 2 * (x.b * x.b) / (x.b * x.b) := by rw [e1]
          _ = 2 := Rat.mul_div_cancel hbb
      exact rat_no_sqrt_two (x.a / x.b) hsq
  · intro h
    subst h
    show (0 : Rat) * 0 - 2 * (0 * 0) = 0
    grind

/-- Componentwise inverse via the conjugate: 1/(a+b√2) = (a-b√2)/(a²-2b²). -/
def inv (x : QS) : QS := ⟨x.a / norm x, -x.b / norm x⟩

instance : Inv QS := ⟨inv⟩

theorem mul_inv_cancel (x : QS) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  have hn : norm x ≠ 0 := fun h0 => hx ((norm_eq_zero_iff x).mp h0)
  have hax : (x.a / norm x) * norm x = x.a := Rat.div_mul_cancel hn
  have hbx : (-x.b / norm x) * norm x = -x.b := Rat.div_mul_cancel hn
  have hfst : x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x)) = 1 := by
    have e1 : (x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x))) * norm x = norm x := by
      have step1 : (x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x))) * norm x
          = x.a * ((x.a / norm x) * norm x) + 2 * (x.b * ((-x.b / norm x) * norm x)) := by
        grind
      rw [step1, hax, hbx]
      show x.a * x.a + 2 * (x.b * -x.b) = x.a * x.a - 2 * (x.b * x.b)
      grind
    have e2 : (x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x)) - 1) * norm x = 0 := by
      have expand : (x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x)) - 1) * norm x
          = (x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x))) * norm x - norm x := by
        grind
      rw [expand, e1]; grind
    rcases Rat.mul_eq_zero.mp e2 with h' | h'
    · grind
    · exact absurd h' hn
  have hsnd : x.a * (-x.b / norm x) + x.b * (x.a / norm x) = 0 := by
    have e1 : (x.a * (-x.b / norm x) + x.b * (x.a / norm x)) * norm x = 0 := by
      have step1 : (x.a * (-x.b / norm x) + x.b * (x.a / norm x)) * norm x
          = x.a * ((-x.b / norm x) * norm x) + x.b * ((x.a / norm x) * norm x) := by
        grind
      rw [step1, hax, hbx]
      grind
    rcases Rat.mul_eq_zero.mp e1 with h' | h'
    · exact h'
    · exact absurd h' hn
  show (⟨x.a * (x.a / norm x) + 2 * (x.b * (-x.b / norm x)),
         x.a * (-x.b / norm x) + x.b * (x.a / norm x)⟩ : QS) = (⟨1, 0⟩ : QS)
  rw [hfst, hsnd]

/-! ## Roadmap Step 3: multiplicative and distributive field laws. -/

theorem mul_assoc (x y z : QS) : (x * y) * z = x * (y * z) := by
  show (⟨(x.a*y.a+2*(x.b*y.b))*z.a+2*((x.a*y.b+x.b*y.a)*z.b),
         (x.a*y.a+2*(x.b*y.b))*z.b+(x.a*y.b+x.b*y.a)*z.a⟩ : QS)
      = ⟨x.a*(y.a*z.a+2*(y.b*z.b))+2*(x.b*(y.a*z.b+y.b*z.a)),
         x.a*(y.a*z.b+y.b*z.a)+x.b*(y.a*z.a+2*(y.b*z.b))⟩
  congr 1 <;> grind

theorem mul_comm (x y : QS) : x * y = y * x := by
  show (⟨x.a*y.a+2*(x.b*y.b), x.a*y.b+x.b*y.a⟩ : QS)
      = ⟨y.a*x.a+2*(y.b*x.b), y.a*x.b+y.b*x.a⟩
  congr 1 <;> grind

theorem one_mul (x : QS) : (1 : QS) * x = x := by
  show (⟨1*x.a+2*(0*x.b), 1*x.b+0*x.a⟩ : QS) = x
  congr 1 <;> grind

theorem mul_one (x : QS) : x * (1 : QS) = x := by
  show (⟨x.a*1+2*(x.b*0), x.a*0+x.b*1⟩ : QS) = x
  congr 1 <;> grind

theorem left_distrib (x y z : QS) : x * (y + z) = x * y + x * z := by
  show (⟨x.a*(y.a+z.a)+2*(x.b*(y.b+z.b)), x.a*(y.b+z.b)+x.b*(y.a+z.a)⟩ : QS)
      = ⟨(x.a*y.a+2*(x.b*y.b))+(x.a*z.a+2*(x.b*z.b)), (x.a*y.b+x.b*y.a)+(x.a*z.b+x.b*z.a)⟩
  congr 1 <;> grind

theorem right_distrib (x y z : QS) : (x + y) * z = x * z + y * z := by
  show (⟨(x.a+y.a)*z.a+2*((x.b+y.b)*z.b), (x.a+y.a)*z.b+(x.b+y.b)*z.a⟩ : QS)
      = ⟨(x.a*z.a+2*(x.b*z.b))+(y.a*z.a+2*(y.b*z.b)), (x.a*z.b+x.b*z.a)+(y.a*z.b+y.b*z.a)⟩
  congr 1 <;> grind

/-! ## Roadmap Step 5 (order-addition compatibility; proved here since it needs
    no positivity-closure machinery, unlike transitivity below). -/

theorem add_lt_add_left (x y z : QS) (h : x < y) : z + x < z + y := by
  show Pos (⟨(z.a + y.a) - (z.a + x.a), (z.b + y.b) - (z.b + x.b)⟩ : QS)
  have e1 : (z.a + y.a) - (z.a + x.a) = y.a - x.a := by grind
  have e2 : (z.b + y.b) - (z.b + x.b) = y.b - x.b := by grind
  rw [e1, e2]
  exact h

/-! ## Roadmap Step 4: trichotomy for arbitrary elements.

    A single QS element's sign (Pos z ∨ z = 0 ∨ Pos(-z)) is decided by cases
    on the signs of z.a, z.b, using `rat_trich` and `norm_eq_zero_iff` exactly
    as the roadmap prescribes: when a,b have the same sign the answer is
    immediate; when they differ, comparing a² to 2b² decides it, and the tie
    case a²=2b² (b≠0) is excluded by `norm_eq_zero_iff`/`rat_no_sqrt_two`. -/

theorem pos_trichotomy (z : QS) : Pos z ∨ z = 0 ∨ Pos (⟨-z.a, -z.b⟩ : QS) := by
  rcases rat_trich z.b 0 with hb | hb | hb
  · -- z.b < 0
    rcases rat_trich z.a 0 with ha | ha | ha
    · -- z.a < 0, z.b < 0 : both strictly negative, -z is branch1
      right; right
      left
      exact ⟨by grind, by grind, Or.inl (by grind)⟩
    · -- z.a = 0, z.b < 0
      right; right
      left
      exact ⟨by grind, by grind, Or.inr (by grind)⟩
    · -- 0 < z.a, z.b < 0 : compare squares
      rcases rat_trich (2 * (z.b * z.b)) (z.a * z.a) with hcmp | hcmp | hcmp
      · -- 2b² < a² : Pos z, branch2
        left
        exact Or.inr (Or.inl ⟨by grind, hb, hcmp⟩)
      · -- 2b² = a² : contradicts irrationality, since z.b ≠ 0
        exfalso
        have hn : norm z = 0 := by show z.a * z.a - 2 * (z.b * z.b) = 0; grind
        have hz0 := (norm_eq_zero_iff z).mp hn
        have hzb : z.b = 0 := by rw [hz0]; rfl
        grind
      · -- a² < 2b² : Pos(-z), branch3
        right; right
        exact Or.inr (Or.inr ⟨by grind, by grind, by grind⟩)
  · -- z.b = 0
    rcases rat_trich z.a 0 with ha | ha | ha
    · right; right
      left
      exact ⟨by grind, by grind, Or.inl (by grind)⟩
    · right; left
      show (⟨z.a, z.b⟩ : QS) = (⟨0, 0⟩ : QS)
      rw [ha, hb]
    · left
      exact Or.inl ⟨by grind, by grind, Or.inl ha⟩
  · -- 0 < z.b
    rcases rat_trich z.a 0 with ha | ha | ha
    · -- z.a < 0, 0 < z.b : compare squares
      rcases rat_trich (z.a * z.a) (2 * (z.b * z.b)) with hcmp | hcmp | hcmp
      · -- a² < 2b² : Pos z, branch3
        left
        exact Or.inr (Or.inr ⟨ha, by grind, hcmp⟩)
      · -- a² = 2b² : contradicts irrationality
        exfalso
        have hn : norm z = 0 := by show z.a * z.a - 2 * (z.b * z.b) = 0; grind
        have hz0 := (norm_eq_zero_iff z).mp hn
        have hzb : z.b = 0 := by rw [hz0]; rfl
        grind
      · -- 2b² < a² : Pos(-z), branch2
        right; right
        exact Or.inr (Or.inl ⟨by grind, by grind, by grind⟩)
    · left
      exact Or.inl ⟨by grind, by grind, Or.inr hb⟩
    · left
      exact Or.inl ⟨by grind, by grind, Or.inl ha⟩

/-! ## Helper lemmas for closure of Pos under addition.

    `le_of_sq_le`/`sqLe_add` handle the "same-direction dominance" cases
    (both summands a-dominant, or both b-dominant) via a Cauchy-Schwarz-style
    argument. `sq_le_sq_of_nonneg`/`sq_lt_sq_of_nonneg` are the easy forward
    direction, used for the branch1-involving cases. The genuinely hard
    "opposite-direction dominance" case (one summand a-dominant, the other
    b-dominant) is handled separately below by `mixed_not_neg`, using an
    explicit rational cross-multiplication certificate (no square roots). -/

theorem sq_le_sq_of_nonneg {p q : Rat} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p ≤ q) :
    p * p ≤ q * q := by
  have h1 : p * p ≤ p * q := Rat.mul_le_mul_of_nonneg_left h hp
  have h2 : p * q ≤ q * q := Rat.mul_le_mul_of_nonneg_right h hq
  exact Rat.le_trans h1 h2

theorem sq_lt_sq_of_nonneg {p q : Rat} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p < q) :
    p * p < q * q := by
  rcases Rat.le_iff_lt_or_eq.mp hq with hq' | hq'
  · have h1 : p * p ≤ p * q := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h) hp
    have h2 : p * q < q * q := Rat.mul_lt_mul_of_pos_right h hq'
    grind
  · exfalso; grind

theorem le_of_sq_le {u v : Rat} (hv : 0 ≤ v) (h : u * u ≤ v * v) : u ≤ v := by
  rcases Rat.le_total (a := u) (b := v) with hle | hge
  · exact hle
  · rcases Rat.le_iff_lt_or_eq.mp hge with hlt | heq
    · exfalso
      have h1 : v * v ≤ v * u := by
        have : 0 ≤ u - v := by grind
        have := Rat.mul_nonneg hv this
        grind
      have h2 : v * u < u * u := by
        have : 0 < u - v := by grind
        have hu_pos : 0 < u := by grind
        have := Rat.mul_pos this hu_pos
        grind
      have h_strict : v * v < u * u := by grind
      have : ¬ (u * u ≤ v * v) := Rat.not_le.mpr h_strict
      exact this h
    · grind

theorem sqLe_add {p₁ q₁ p₂ q₂ : Rat}
    (hp₁ : 0 ≤ p₁) (hq₁ : 0 ≤ q₁) (hp₂ : 0 ≤ p₂) (hq₂ : 0 ≤ q₂)
    (h₁ : 2 * (q₁ * q₁) ≤ p₁ * p₁) (h₂ : 2 * (q₂ * q₂) ≤ p₂ * p₂) :
    2 * ((q₁ + q₂) * (q₁ + q₂)) ≤ (p₁ + p₂) * (p₁ + p₂) := by
  have hA : 0 ≤ 2 * (q₁ * q₂) := by
    have := Rat.mul_nonneg hq₁ hq₂
    grind
  have hB : 0 ≤ p₁ * p₂ := Rat.mul_nonneg hp₁ hp₂
  have hsq : (2 * (q₁ * q₂)) * (2 * (q₁ * q₂)) ≤ (p₁ * p₂) * (p₁ * p₂) := by
    have e1 : (2 * (q₁ * q₂)) * (2 * (q₁ * q₂)) = (2 * (q₁ * q₁)) * (2 * (q₂ * q₂)) := by grind
    have e2 : (p₁ * p₂) * (p₁ * p₂) = (p₁ * p₁) * (p₂ * p₂) := by grind
    rw [e1, e2]
    have n1 : 0 ≤ 2 * (q₁ * q₁) := by
      have := Rat.mul_nonneg hq₁ hq₁
      grind
    have n2 : 0 ≤ p₂ * p₂ := Rat.mul_nonneg hp₂ hp₂
    have step1 : (2 * (q₁ * q₁)) * (2 * (q₂ * q₂)) ≤ (2 * (q₁ * q₁)) * (p₂ * p₂) := by
      have hdiff : 0 ≤ p₂ * p₂ - 2 * (q₂ * q₂) := by grind
      have := Rat.mul_nonneg n1 hdiff
      grind
    have step2 : (2 * (q₁ * q₁)) * (p₂ * p₂) ≤ (p₁ * p₁) * (p₂ * p₂) := by
      have hdiff : 0 ≤ p₁ * p₁ - 2 * (q₁ * q₁) := by grind
      have := Rat.mul_nonneg hdiff n2
      grind
    exact Rat.le_trans step1 step2
  have hmix : 2 * (q₁ * q₂) ≤ p₁ * p₂ := le_of_sq_le hB hsq
  grind

/-- The hard case: one summand is a-dominant (U,-B, with U²>2B²), the other is
    b-dominant (-A,V, with A²<2V²), opposite directions. Shows their sum's
    negation can't be positive, i.e. the sum itself isn't negative — via two
    pure polynomial identities (no square roots): `V*(U-A) - A*(B-V) = UV-AB`
    and `B*(U-A) - U*(B-V) = UV-AB`, each turning one branch of `Pos` applied
    to `⟨A-U, B-V⟩` into a contradiction once `U*V > A*B` is established. -/
theorem dominance_mul_lt (U B A V : Rat)
    (hU : 0 < U) (hB : 0 < B) (hA : 0 < A) (hV : 0 < V)
    (hD1 : 2 * (B * B) < U * U) (hD2 : A * A < 2 * (V * V)) :
    A * B < U * V := by
  apply Classical.byContradiction
  intro hcon
  have hcon' : U * V ≤ A * B := Rat.not_lt.mp hcon
  have hsq : (U * V) * (U * V) ≤ (A * B) * (A * B) :=
    sq_le_sq_of_nonneg (Rat.mul_nonneg (Rat.le_of_lt hU) (Rat.le_of_lt hV))
      (Rat.mul_nonneg (Rat.le_of_lt hA) (Rat.le_of_lt hB)) hcon'
  have hpos : 0 < (U * U - 2 * (B * B)) * (V * V) + (2 * (V * V) - A * A) * (B * B) := by
    have t1 : 0 < (U * U - 2 * (B * B)) * (V * V) :=
      Rat.mul_pos (by grind) (Rat.mul_pos hV hV)
    have t2 : 0 < (2 * (V * V) - A * A) * (B * B) :=
      Rat.mul_pos (by grind) (Rat.mul_pos hB hB)
    grind
  grind

theorem mixed_not_neg (U B A V : Rat)
    (hU : 0 < U) (hB : 0 < B) (hA : 0 < A) (hV : 0 < V)
    (hD1 : 2 * (B * B) < U * U) (hD2 : A * A < 2 * (V * V)) :
    ¬ Pos (⟨A - U, B - V⟩ : QS) := by
  have hUV : A * B < U * V := dominance_mul_lt U B A V hU hB hA hV hD1 hD2
  intro hpos
  unfold Pos at hpos
  simp only at hpos
  rcases hpos with h | h | h
  · -- branch1: A-U≥0 ∧ B-V≥0 ⟹ AB≥UV, contradicting hUV
    obtain ⟨h1, h2, _⟩ := h
    have hAB : U * B ≤ A * B :=
      Rat.mul_le_mul_of_nonneg_right (by grind : U ≤ A) (Rat.le_of_lt hB)
    have hUV' : U * V ≤ U * B :=
      Rat.mul_le_mul_of_nonneg_left (by grind : V ≤ B) (Rat.le_of_lt hU)
    grind
  · -- branch2: A-U≥0 ∧ B-V<0 ∧ 2(B-V)²<(A-U)² ; contradicts via hD2
    obtain ⟨h1, h2, h3⟩ := h
    have key : V * (A - U) < A * (V - B) := by grind
    have hVB : 0 < V - B := by grind
    have hsq2 : (V * (A - U)) * (V * (A - U)) < (A * (V - B)) * (A * (V - B)) := by
      apply sq_lt_sq_of_nonneg
      · exact Rat.mul_nonneg (Rat.le_of_lt hV) h1
      · exact Rat.mul_nonneg (Rat.le_of_lt hA) (Rat.le_of_lt hVB)
      · exact key
    have hbound : (A * (V - B)) * (A * (V - B)) < (2 * (V * V)) * ((V - B) * (V - B)) := by
      have hVBsq : 0 < (V - B) * (V - B) := Rat.mul_pos hVB hVB
      have e1 : (A * (V - B)) * (A * (V - B)) = (A * A) * ((V - B) * (V - B)) := by grind
      rw [e1]
      exact (Rat.mul_lt_mul_right hVBsq).mpr hD2
    have hchain : (V * V) * ((U - A) * (U - A)) < (V * V) * (2 * ((V - B) * (V - B))) := by
      have e1 : (V * (A - U)) * (V * (A - U)) = (V * V) * ((U - A) * (U - A)) := by grind
      have e3 : (2 * (V * V)) * ((V - B) * (V - B)) = (V * V) * (2 * ((V - B) * (V - B))) := by
        grind
      rw [e3] at hbound
      rw [e1] at hsq2
      grind
    have hVsq : 0 < V * V := Rat.mul_pos hV hV
    have hfin : (U - A) * (U - A) < 2 * ((V - B) * (V - B)) :=
      (Rat.mul_lt_mul_left hVsq).mp hchain
    have hVBeq : (V - B) * (V - B) = (B - V) * (B - V) := by grind
    have hUAeq : (U - A) * (U - A) = (A - U) * (A - U) := by grind
    rw [hVBeq, hUAeq] at hfin
    grind
  · -- branch3: A-U<0 ∧ B-V≥0 ∧ (A-U)²<2(B-V)² ; contradicts via hD1
    obtain ⟨h1, h2, h3⟩ := h
    have key : U * (B - V) < B * (U - A) := by grind
    have hUA : 0 < U - A := by grind
    have hsq1 : (U * (B - V)) * (U * (B - V)) < (B * (U - A)) * (B * (U - A)) := by
      apply sq_lt_sq_of_nonneg
      · exact Rat.mul_nonneg (Rat.le_of_lt hU) h2
      · exact Rat.mul_nonneg (Rat.le_of_lt hB) (Rat.le_of_lt hUA)
      · exact key
    have hbound : (2 * (B * B)) * ((B - V) * (B - V)) ≤ (U * U) * ((B - V) * (B - V)) := by
      have hBVsq : 0 ≤ (B - V) * (B - V) := Rat.mul_nonneg h2 h2
      exact Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hD1) hBVsq
    have hchain : (2 * (B * B)) * ((B - V) * (B - V)) < (B * B) * ((U - A) * (U - A)) := by
      have e1 : (U * (B - V)) * (U * (B - V)) = (U * U) * ((B - V) * (B - V)) := by grind
      have e2 : (B * (U - A)) * (B * (U - A)) = (B * B) * ((U - A) * (U - A)) := by grind
      rw [e1, e2] at hsq1
      grind
    have hBsq : 0 < B * B := Rat.mul_pos hB hB
    have hfin : 2 * ((B - V) * (B - V)) < (U - A) * (U - A) := by
      have e : (2 * (B * B)) * ((B - V) * (B - V)) = (B * B) * (2 * ((B - V) * (B - V))) := by
        grind
      rw [e] at hchain
      exact (Rat.mul_lt_mul_left hBsq).mp hchain
    have hUAeq : (U - A) * (U - A) = (A - U) * (A - U) := by grind
    rw [hUAeq] at hfin
    grind

theorem sqLe_add2 {p₁ q₁ p₂ q₂ : Rat}
    (hp₁ : 0 ≤ p₁) (hq₁ : 0 ≤ q₁) (hp₂ : 0 ≤ p₂) (hq₂ : 0 ≤ q₂)
    (h₁ : p₁ * p₁ ≤ 2 * (q₁ * q₁)) (h₂ : p₂ * p₂ ≤ 2 * (q₂ * q₂)) :
    (p₁ + p₂) * (p₁ + p₂) ≤ 2 * ((q₁ + q₂) * (q₁ + q₂)) := by
  have hA : 0 ≤ p₁ * p₂ := Rat.mul_nonneg hp₁ hp₂
  have hB : 0 ≤ 2 * (q₁ * q₂) := by
    have := Rat.mul_nonneg hq₁ hq₂; grind
  have hsq : (p₁ * p₂) * (p₁ * p₂) ≤ (2 * (q₁ * q₂)) * (2 * (q₁ * q₂)) := by
    have e1 : (p₁ * p₂) * (p₁ * p₂) = (p₁ * p₁) * (p₂ * p₂) := by grind
    have e2 : (2 * (q₁ * q₂)) * (2 * (q₁ * q₂)) = (2 * (q₁ * q₁)) * (2 * (q₂ * q₂)) := by grind
    rw [e1, e2]
    have n1 : 0 ≤ p₂ * p₂ := Rat.mul_nonneg hp₂ hp₂
    have n2 : 0 ≤ 2 * (q₁ * q₁) := by have := Rat.mul_nonneg hq₁ hq₁; grind
    have step1 : (p₁ * p₁) * (p₂ * p₂) ≤ (2 * (q₁ * q₁)) * (p₂ * p₂) := by
      have hdiff : 0 ≤ 2 * (q₁ * q₁) - p₁ * p₁ := by grind
      have := Rat.mul_nonneg hdiff n1
      grind
    have step2 : (2 * (q₁ * q₁)) * (p₂ * p₂) ≤ (2 * (q₁ * q₁)) * (2 * (q₂ * q₂)) := by
      have hdiff : 0 ≤ 2 * (q₂ * q₂) - p₂ * p₂ := by grind
      have := Rat.mul_nonneg n2 hdiff
      grind
    exact Rat.le_trans step1 step2
  have hmix : p₁ * p₂ ≤ 2 * (q₁ * q₂) := le_of_sq_le hB hsq
  grind

/-- x is branch1 (both components ≥ 0), y is any positive element: the sum is
    positive. This is the "monotonic" case — adding a nonnegative-nonnegative
    element only helps, no square-root-scale argument is needed, just
    comparing y's own components to the shifted sum. -/
theorem pos_add_branch1_left (x y : QS) (hxa : 0 ≤ x.a) (hxb : 0 ≤ x.b) (hy : Pos y) :
    Pos (⟨x.a + y.a, x.b + y.b⟩ : QS) := by
  rcases hy with h | h | h
  · obtain ⟨ha, hb, hor⟩ := h
    refine Or.inl ⟨by grind, by grind, ?_⟩
    rcases hor with h' | h'
    · left; grind
    · right; grind
  · obtain ⟨ha, hb, hsq⟩ := h
    have hya : 0 < y.a := by
      rcases Rat.le_iff_lt_or_eq.mp ha with h' | h'
      · exact h'
      · exfalso
        have hz : y.a = 0 := h'.symm
        have hnn : (0 : Rat) ≤ y.b * y.b := sq_nonneg y.b
        rw [hz] at hsq
        grind
    rcases rat_trich (x.b + y.b) 0 with hs | hs | hs
    · refine Or.inr (Or.inl ⟨by grind, hs, ?_⟩)
      have hb2 : (x.b + y.b) * (x.b + y.b) ≤ y.b * y.b := by
        have key := sq_le_sq_of_nonneg (p := -(x.b + y.b)) (q := -y.b)
          (by grind) (by grind) (by grind)
        grind
      have ha2 : y.a * y.a ≤ (x.a + y.a) * (x.a + y.a) := by
        have key := sq_le_sq_of_nonneg (p := y.a) (q := x.a + y.a)
          (by grind) (by grind) (by grind)
        grind
      grind
    · exact Or.inl ⟨by grind, by grind, Or.inl (by grind)⟩
    · exact Or.inl ⟨by grind, by grind, Or.inl (by grind)⟩
  · obtain ⟨ha, hb, hsq⟩ := h
    have hyb : 0 < y.b := by
      rcases Rat.le_iff_lt_or_eq.mp hb with h' | h'
      · exact h'
      · exfalso
        have hz : y.b = 0 := h'.symm
        have hnn : (0 : Rat) ≤ y.a * y.a := sq_nonneg y.a
        rw [hz] at hsq
        grind
    rcases rat_trich (x.a + y.a) 0 with hs | hs | hs
    · refine Or.inr (Or.inr ⟨hs, by grind, ?_⟩)
      have ha2 : (x.a + y.a) * (x.a + y.a) ≤ y.a * y.a := by
        have key := sq_le_sq_of_nonneg (p := -(x.a + y.a)) (q := -y.a)
          (by grind) (by grind) (by grind)
        grind
      have hb2 : y.b * y.b ≤ (x.b + y.b) * (x.b + y.b) := by
        have key := sq_le_sq_of_nonneg (p := y.b) (q := x.b + y.b)
          (by grind) (by grind) (by grind)
        grind
      grind
    · exact Or.inl ⟨by grind, by grind, Or.inr (by grind)⟩
    · exact Or.inl ⟨by grind, by grind, Or.inr (by grind)⟩

/-- Positivity is closed under addition. Nine cases from the two branches of
    `Pos x` × `Pos y`: branch1-involving cases reduce to `pos_add_branch1_left`
    (monotonicity); same-direction cases (2+2, 3+3) reduce to `sqLe_add`/
    `sqLe_add2` (Cauchy-Schwarz) with a strictness upgrade via
    `norm_eq_zero_iff`; opposite-direction cases (2+3, 3+2) reduce to
    `mixed_not_neg` via `pos_trichotomy` on the sum. -/
theorem pos_add (x y : QS) (hx : Pos x) (hy : Pos y) :
    Pos (⟨x.a + y.a, x.b + y.b⟩ : QS) := by
  rcases hx with hx1 | hx2 | hx3
  · obtain ⟨hxa, hxb, _⟩ := hx1
    exact pos_add_branch1_left x y hxa hxb hy
  · rcases hy with hy1 | hy2 | hy3
    · obtain ⟨hya, hyb, _⟩ := hy1
      have hswap := pos_add_branch1_left y x hya hyb (Or.inr (Or.inl hx2))
      have e : (⟨y.a + x.a, y.b + x.b⟩ : QS) = (⟨x.a + y.a, x.b + y.b⟩ : QS) := by
        congr 1 <;> grind
      rwa [e] at hswap
    · -- branch2 + branch2
      obtain ⟨hx2a, hx2b, hx2sq⟩ := hx2
      obtain ⟨hy2a, hy2b, hy2sq⟩ := hy2
      have hxa_pos : 0 < x.a := by
        rcases Rat.le_iff_lt_or_eq.mp hx2a with h' | h'
        · exact h'
        · exfalso
          have hz : x.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.b * x.b := sq_nonneg x.b
          rw [hz] at hx2sq; grind
      have hya_pos : 0 < y.a := by
        rcases Rat.le_iff_lt_or_eq.mp hy2a with h' | h'
        · exact h'
        · exfalso
          have hz : y.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.b * y.b := sq_nonneg y.b
          rw [hz] at hy2sq; grind
      have hle : 2 * ((x.b + y.b) * (x.b + y.b)) ≤ (x.a + y.a) * (x.a + y.a) := by
        have key := sqLe_add (p₁ := x.a) (q₁ := -x.b) (p₂ := y.a) (q₂ := -y.b)
          (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        grind
      refine Or.inr (Or.inl ⟨by grind, by grind, ?_⟩)
      rcases Rat.le_iff_lt_or_eq.mp hle with hlt | heq
      · exact hlt
      · exfalso
        have hn0 : norm (⟨x.a + y.a, x.b + y.b⟩ : QS) = 0 := by
          show (x.a + y.a) * (x.a + y.a) - 2 * ((x.b + y.b) * (x.b + y.b)) = 0
          grind
        have hz0 : (⟨x.a + y.a, x.b + y.b⟩ : QS) = (⟨0, 0⟩ : QS) := (norm_eq_zero_iff _).mp hn0
        have hbz : x.a + y.a = 0 := congrArg QS.a hz0
        grind
    · -- branch2 + branch3 (opposite dominance)
      obtain ⟨hx2a, hx2b, hx2sq⟩ := hx2
      obtain ⟨hy3a, hy3b, hy3sq⟩ := hy3
      have hxa_pos : 0 < x.a := by
        rcases Rat.le_iff_lt_or_eq.mp hx2a with h' | h'
        · exact h'
        · exfalso
          have hz : x.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.b * x.b := sq_nonneg x.b
          rw [hz] at hx2sq; grind
      have hyb_pos : 0 < y.b := by
        rcases Rat.le_iff_lt_or_eq.mp hy3b with h' | h'
        · exact h'
        · exfalso
          have hz : y.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.a * y.a := sq_nonneg y.a
          rw [hz] at hy3sq; grind
      have hUV : (-y.a) * (-x.b) < x.a * y.b :=
        dominance_mul_lt x.a (-x.b) (-y.a) y.b hxa_pos (by grind) (by grind) hyb_pos
          (by grind) (by grind)
      have hmixed := mixed_not_neg x.a (-x.b) (-y.a) y.b hxa_pos (by grind) (by grind) hyb_pos
        (by grind) (by grind)
      rcases pos_trichotomy (⟨x.a + y.a, x.b + y.b⟩ : QS) with hp | hz | hn
      · exact hp
      · exfalso
        have hz0 : (⟨x.a + y.a, x.b + y.b⟩ : QS) = (⟨0, 0⟩ : QS) := hz
        have ha' : x.a + y.a = 0 := congrArg QS.a hz0
        have hb' : x.b + y.b = 0 := congrArg QS.b hz0
        have hxa_eq : x.a = -y.a := by grind
        have hxb_eq : x.b = -y.b := by grind
        rw [hxa_eq, hxb_eq] at hUV
        grind
      · exfalso
        apply hmixed
        have e : (⟨(-y.a) - x.a, (-x.b) - y.b⟩ : QS) = (⟨-(x.a + y.a), -(x.b + y.b)⟩ : QS) := by
          congr 1 <;> grind
        rw [e]
        exact hn
  · rcases hy with hy1 | hy2 | hy3
    · obtain ⟨hya, hyb, _⟩ := hy1
      have hswap := pos_add_branch1_left y x hya hyb (Or.inr (Or.inr hx3))
      have e : (⟨y.a + x.a, y.b + x.b⟩ : QS) = (⟨x.a + y.a, x.b + y.b⟩ : QS) := by
        congr 1 <;> grind
      rwa [e] at hswap
    · -- branch3 + branch2 (opposite dominance, mirrored)
      obtain ⟨hx3a, hx3b, hx3sq⟩ := hx3
      obtain ⟨hy2a, hy2b, hy2sq⟩ := hy2
      have hya_pos : 0 < y.a := by
        rcases Rat.le_iff_lt_or_eq.mp hy2a with h' | h'
        · exact h'
        · exfalso
          have hz : y.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.b * y.b := sq_nonneg y.b
          rw [hz] at hy2sq; grind
      have hxb_pos : 0 < x.b := by
        rcases Rat.le_iff_lt_or_eq.mp hx3b with h' | h'
        · exact h'
        · exfalso
          have hz : x.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.a * x.a := sq_nonneg x.a
          rw [hz] at hx3sq; grind
      have hUV : (-x.a) * (-y.b) < y.a * x.b :=
        dominance_mul_lt y.a (-y.b) (-x.a) x.b hya_pos (by grind) (by grind) hxb_pos
          (by grind) (by grind)
      have hmixed := mixed_not_neg y.a (-y.b) (-x.a) x.b hya_pos (by grind) (by grind) hxb_pos
        (by grind) (by grind)
      rcases pos_trichotomy (⟨x.a + y.a, x.b + y.b⟩ : QS) with hp | hz | hn
      · exact hp
      · exfalso
        have hz0 : (⟨x.a + y.a, x.b + y.b⟩ : QS) = (⟨0, 0⟩ : QS) := hz
        have ha' : x.a + y.a = 0 := congrArg QS.a hz0
        have hb' : x.b + y.b = 0 := congrArg QS.b hz0
        have hya_eq : y.a = -x.a := by grind
        have hyb_eq : y.b = -x.b := by grind
        rw [hya_eq, hyb_eq] at hUV
        grind
      · exfalso
        apply hmixed
        have e : (⟨(-x.a) - y.a, (-y.b) - x.b⟩ : QS) = (⟨-(x.a + y.a), -(x.b + y.b)⟩ : QS) := by
          congr 1 <;> grind
        rw [e]
        exact hn
    · -- branch3 + branch3
      obtain ⟨hx3a, hx3b, hx3sq⟩ := hx3
      obtain ⟨hy3a, hy3b, hy3sq⟩ := hy3
      have hxb_pos : 0 < x.b := by
        rcases Rat.le_iff_lt_or_eq.mp hx3b with h' | h'
        · exact h'
        · exfalso
          have hz : x.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.a * x.a := sq_nonneg x.a
          rw [hz] at hx3sq; grind
      have hyb_pos : 0 < y.b := by
        rcases Rat.le_iff_lt_or_eq.mp hy3b with h' | h'
        · exact h'
        · exfalso
          have hz : y.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.a * y.a := sq_nonneg y.a
          rw [hz] at hy3sq; grind
      have hle : (x.a + y.a) * (x.a + y.a) ≤ 2 * ((x.b + y.b) * (x.b + y.b)) := by
        have key := sqLe_add2 (p₁ := -x.a) (q₁ := x.b) (p₂ := -y.a) (q₂ := y.b)
          (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        grind
      have hsuma_neg : x.a + y.a < 0 := by grind
      refine Or.inr (Or.inr ⟨hsuma_neg, by grind, ?_⟩)
      rcases Rat.le_iff_lt_or_eq.mp hle with hlt | heq
      · exact hlt
      · exfalso
        have hn0 : norm (⟨x.a + y.a, x.b + y.b⟩ : QS) = 0 := by
          show (x.a + y.a) * (x.a + y.a) - 2 * ((x.b + y.b) * (x.b + y.b)) = 0
          grind
        have hz0 : (⟨x.a + y.a, x.b + y.b⟩ : QS) = (⟨0, 0⟩ : QS) := (norm_eq_zero_iff _).mp hn0
        have hbz : x.b + y.b = 0 := congrArg QS.b hz0
        grind

theorem trichotomy (x y : QS) : x < y ∨ x = y ∨ y < x := by
  rcases pos_trichotomy (⟨y.a - x.a, y.b - x.b⟩ : QS) with h | h | h
  · left; exact h
  · right; left
    have h' : (⟨y.a - x.a, y.b - x.b⟩ : QS) = (⟨0, 0⟩ : QS) := h
    have ha' : y.a - x.a = 0 := congrArg QS.a h'
    have hb' : y.b - x.b = 0 := congrArg QS.b h'
    show (⟨x.a, x.b⟩ : QS) = (⟨y.a, y.b⟩ : QS)
    have hae : x.a = y.a := by grind
    have hbe : x.b = y.b := by grind
    rw [hae, hbe]
  · right; right
    show Pos (⟨x.a - y.a, x.b - y.b⟩ : QS)
    have e1 : x.a - y.a = -(y.a - x.a) := by grind
    have e2 : x.b - y.b = -(y.b - x.b) := by grind
    rw [e1, e2]
    exact h

theorem transitivity (x y z : QS) (hxy : x < y) (hyz : y < z) : x < z := by
  show Pos (⟨z.a - x.a, z.b - x.b⟩ : QS)
  have hu : Pos (⟨y.a - x.a, y.b - x.b⟩ : QS) := hxy
  have hv : Pos (⟨z.a - y.a, z.b - y.b⟩ : QS) := hyz
  have hsum := pos_add (⟨y.a - x.a, y.b - x.b⟩ : QS) (⟨z.a - y.a, z.b - y.b⟩ : QS) hu hv
  have ea : (y.a - x.a) + (z.a - y.a) = z.a - x.a := by grind
  have eb : (y.b - x.b) + (z.b - y.b) = z.b - x.b := by grind
  rw [ea, eb] at hsum
  exact hsum

/-! ## Roadmap Step 5: positivity closed under multiplication.

    Unlike addition, multiplication needs no cross-dominance trick: any
    branch1 (nonnegative-pair) factor decomposes as
    `x = emb x.a + emb x.b * s`, and both positive-scalar multiplication
    (`pos_scale`) and multiplication by `s` alone (`pos_s_mul`) preserve
    positivity with no ambiguity, so `pos_add` finishes those cases. The
    remaining branch2/branch3 combinations have components with an
    unconditional sign (verified directly), and `norm_mul` supplies the
    needed square inequality from the sign of `norm x * norm y`. -/

theorem norm_mul (x y : QS) : norm (x * y) = norm x * norm y := by
  show (x.a * y.a + 2 * (x.b * y.b)) * (x.a * y.a + 2 * (x.b * y.b))
      - 2 * ((x.a * y.b + x.b * y.a) * (x.a * y.b + x.b * y.a))
      = (x.a * x.a - 2 * (x.b * x.b)) * (y.a * y.a - 2 * (y.b * y.b))
  grind

theorem pos_scale (q : Rat) (hq : 0 < q) (y : QS) (hy : Pos y) : Pos (emb q * y) := by
  show Pos (⟨q * y.a + 2 * (0 * y.b), q * y.b + 0 * y.a⟩ : QS)
  rcases hy with h | h | h
  · obtain ⟨ha, hb, hor⟩ := h
    have hqa : 0 ≤ q * y.a := Rat.mul_nonneg (Rat.le_of_lt hq) ha
    have hqb : 0 ≤ q * y.b := Rat.mul_nonneg (Rat.le_of_lt hq) hb
    refine Or.inl ⟨by grind, by grind, ?_⟩
    rcases hor with h' | h'
    · left; have := Rat.mul_pos hq h'; grind
    · right; have := Rat.mul_pos hq h'; grind
  · obtain ⟨ha, hb, hsq⟩ := h
    have hqa : 0 ≤ q * y.a := Rat.mul_nonneg (Rat.le_of_lt hq) ha
    have hqb : q * y.b < 0 := by
      have := Rat.mul_pos hq (by grind : 0 < -y.b); grind
    refine Or.inr (Or.inl ⟨by grind, by grind, ?_⟩)
    have hq2 : 0 < q * q := Rat.mul_pos hq hq
    have step : q * q * (2 * (y.b * y.b)) < q * q * (y.a * y.a) :=
      (Rat.mul_lt_mul_left hq2).mpr hsq
    have e1 : 2 * ((q * y.b + 0 * y.a) * (q * y.b + 0 * y.a)) = q * q * (2 * (y.b * y.b)) := by
      grind
    have e2 : (q * y.a + 2 * (0 * y.b)) * (q * y.a + 2 * (0 * y.b)) = q * q * (y.a * y.a) := by
      grind
    rw [e1, e2]; exact step
  · obtain ⟨ha, hb, hsq⟩ := h
    have hqa : q * y.a < 0 := by
      have := Rat.mul_pos hq (by grind : 0 < -y.a); grind
    have hqb : 0 ≤ q * y.b := Rat.mul_nonneg (Rat.le_of_lt hq) hb
    refine Or.inr (Or.inr ⟨by grind, by grind, ?_⟩)
    have hq2 : 0 < q * q := Rat.mul_pos hq hq
    have step : q * q * (y.a * y.a) < q * q * (2 * (y.b * y.b)) :=
      (Rat.mul_lt_mul_left hq2).mpr hsq
    have e1 : (q * y.a + 2 * (0 * y.b)) * (q * y.a + 2 * (0 * y.b)) = q * q * (y.a * y.a) := by
      grind
    have e2 : 2 * ((q * y.b + 0 * y.a) * (q * y.b + 0 * y.a)) = q * q * (2 * (y.b * y.b)) := by
      grind
    rw [e1, e2]; exact step

theorem pos_s_mul (y : QS) (hy : Pos y) : Pos (s * y) := by
  show Pos (⟨0 * y.a + 2 * (1 * y.b), 0 * y.b + 1 * y.a⟩ : QS)
  rcases hy with h | h | h
  · obtain ⟨ha, hb, hor⟩ := h
    refine Or.inl ⟨by grind, by grind, ?_⟩
    rcases hor with h' | h'
    · right; grind
    · left; grind
  · obtain ⟨ha, hb, hsq⟩ := h
    exact Or.inr (Or.inr ⟨by grind, by grind, by grind⟩)
  · obtain ⟨ha, hb, hsq⟩ := h
    exact Or.inr (Or.inl ⟨by grind, by grind, by grind⟩)

theorem pos_mul_branch1_left (x y : QS) (hxa : 0 ≤ x.a) (hxb : 0 ≤ x.b)
    (hor : 0 < x.a ∨ 0 < x.b) (hy : Pos y) : Pos (x * y) := by
  have hdecomp : x = emb x.a + emb x.b * s := by
    show (⟨x.a, x.b⟩ : QS)
        = (⟨x.a + (x.b * 0 + 2 * (0 * 1)), 0 + (x.b * 1 + 0 * 0)⟩ : QS)
    congr 1 <;> grind
  rw [hdecomp, right_distrib, mul_assoc]
  rcases hor with h' | h'
  · have hp1 : Pos (emb x.a * y) := pos_scale x.a h' y hy
    rcases Rat.le_iff_lt_or_eq.mp hxb with h'' | h''
    · exact pos_add (emb x.a * y) (emb x.b * (s * y)) hp1
        (pos_scale x.b h'' (s * y) (pos_s_mul y hy))
    · have hz : emb x.b * (s * y) = (0 : QS) := by
        have hxbz : x.b = 0 := h''.symm
        show (⟨x.b * (s * y).a + 2 * (0 * (s * y).b), x.b * (s * y).b + 0 * (s * y).a⟩ : QS)
            = (⟨0, 0⟩ : QS)
        rw [hxbz]; grind
      rw [hz, add_zero]
      exact hp1
  · have hp2 : Pos (emb x.b * (s * y)) := pos_scale x.b h' (s * y) (pos_s_mul y hy)
    rcases Rat.le_iff_lt_or_eq.mp hxa with h'' | h''
    · exact pos_add (emb x.a * y) (emb x.b * (s * y)) (pos_scale x.a h'' y hy) hp2
    · have hz : emb x.a * y = (0 : QS) := by
        have hxaz : x.a = 0 := h''.symm
        show (⟨x.a * y.a + 2 * (0 * y.b), x.a * y.b + 0 * y.a⟩ : QS) = (⟨0, 0⟩ : QS)
        rw [hxaz]; grind
      rw [hz, zero_add]
      exact hp2

theorem mul_pos (x y : QS) (hx : Pos x) (hy : Pos y) : Pos (x * y) := by
  rcases hx with hx1 | hx2 | hx3
  · obtain ⟨hxa, hxb, hor⟩ := hx1
    exact pos_mul_branch1_left x y hxa hxb hor hy
  · rcases hy with hy1 | hy2 | hy3
    · obtain ⟨hya, hyb, hor⟩ := hy1
      have hswap := pos_mul_branch1_left y x hya hyb hor (Or.inr (Or.inl hx2))
      have e : y * x = x * y := mul_comm y x
      rwa [e] at hswap
    · -- branch2 + branch2 → branch2
      obtain ⟨hxa, hxb, hxsq⟩ := hx2
      obtain ⟨hya, hyb, hysq⟩ := hy2
      have hxa_pos : 0 < x.a := by
        rcases Rat.le_iff_lt_or_eq.mp hxa with h' | h'
        · exact h'
        · exfalso; have hz : x.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.b * x.b := sq_nonneg x.b
          rw [hz] at hxsq; grind
      have hya_pos : 0 < y.a := by
        rcases Rat.le_iff_lt_or_eq.mp hya with h' | h'
        · exact h'
        · exfalso; have hz : y.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.b * y.b := sq_nonneg y.b
          rw [hz] at hysq; grind
      show Pos (⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩ : QS)
      have hsa : 0 ≤ x.a * y.a + 2 * (x.b * y.b) := by
        have t1 : 0 < x.a * y.a := Rat.mul_pos hxa_pos hya_pos
        have t2 : 0 < x.b * y.b := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.b) (by grind : (0:Rat) < -y.b); grind
        grind
      have hsb : x.a * y.b + x.b * y.a < 0 := by
        have t1 : x.a * y.b < 0 := by
          have := Rat.mul_pos hxa_pos (by grind : (0:Rat) < -y.b); grind
        have t2 : x.b * y.a < 0 := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.b) hya_pos; grind
        grind
      have hnx : 0 < norm x := by show 0 < x.a * x.a - 2 * (x.b * x.b); grind
      have hny : 0 < norm y := by show 0 < y.a * y.a - 2 * (y.b * y.b); grind
      have hnxy : 0 < norm (x * y) := by rw [norm_mul]; exact Rat.mul_pos hnx hny
      refine Or.inr (Or.inl ⟨hsa, hsb, ?_⟩)
      have hraw : 0 < (x.a * y.a + 2 * (x.b * y.b)) * (x.a * y.a + 2 * (x.b * y.b))
          - 2 * ((x.a * y.b + x.b * y.a) * (x.a * y.b + x.b * y.a)) := hnxy
      grind
    · -- branch2 + branch3 → branch3
      obtain ⟨hxa, hxb, hxsq⟩ := hx2
      obtain ⟨hya, hyb, hysq⟩ := hy3
      have hxa_pos : 0 < x.a := by
        rcases Rat.le_iff_lt_or_eq.mp hxa with h' | h'
        · exact h'
        · exfalso; have hz : x.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.b * x.b := sq_nonneg x.b
          rw [hz] at hxsq; grind
      have hyb_pos : 0 < y.b := by
        rcases Rat.le_iff_lt_or_eq.mp hyb with h' | h'
        · exact h'
        · exfalso; have hz : y.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.a * y.a := sq_nonneg y.a
          rw [hz] at hysq; grind
      show Pos (⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩ : QS)
      have hsa : x.a * y.a + 2 * (x.b * y.b) < 0 := by
        have t1 : x.a * y.a < 0 := by
          have := Rat.mul_pos hxa_pos (by grind : (0:Rat) < -y.a); grind
        have t2 : x.b * y.b < 0 := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.b) hyb_pos; grind
        grind
      have hsb : 0 < x.a * y.b + x.b * y.a := by
        have t1 : 0 < x.a * y.b := Rat.mul_pos hxa_pos hyb_pos
        have t2 : 0 < x.b * y.a := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.b) (by grind : (0:Rat) < -y.a); grind
        grind
      have hnx : 0 < norm x := by show 0 < x.a * x.a - 2 * (x.b * x.b); grind
      have hny : norm y < 0 := by show y.a * y.a - 2 * (y.b * y.b) < 0; grind
      have hnxy : norm (x * y) < 0 := by
        rw [norm_mul]
        have := Rat.mul_pos hnx (by grind : 0 < -norm y)
        grind
      refine Or.inr (Or.inr ⟨hsa, by grind, ?_⟩)
      have hraw : (x.a * y.a + 2 * (x.b * y.b)) * (x.a * y.a + 2 * (x.b * y.b))
          - 2 * ((x.a * y.b + x.b * y.a) * (x.a * y.b + x.b * y.a)) < 0 := hnxy
      grind
  · rcases hy with hy1 | hy2 | hy3
    · obtain ⟨hya, hyb, hor⟩ := hy1
      have hswap := pos_mul_branch1_left y x hya hyb hor (Or.inr (Or.inr hx3))
      have e : y * x = x * y := mul_comm y x
      rwa [e] at hswap
    · -- branch3 + branch2 → branch3
      obtain ⟨hxa, hxb, hxsq⟩ := hx3
      obtain ⟨hya, hyb, hysq⟩ := hy2
      have hxb_pos : 0 < x.b := by
        rcases Rat.le_iff_lt_or_eq.mp hxb with h' | h'
        · exact h'
        · exfalso; have hz : x.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.a * x.a := sq_nonneg x.a
          rw [hz] at hxsq; grind
      have hya_pos : 0 < y.a := by
        rcases Rat.le_iff_lt_or_eq.mp hya with h' | h'
        · exact h'
        · exfalso; have hz : y.a = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.b * y.b := sq_nonneg y.b
          rw [hz] at hysq; grind
      show Pos (⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩ : QS)
      have hsa : x.a * y.a + 2 * (x.b * y.b) < 0 := by
        have t1 : x.a * y.a < 0 := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.a) hya_pos; grind
        have t2 : x.b * y.b < 0 := by
          have := Rat.mul_pos hxb_pos (by grind : (0:Rat) < -y.b); grind
        grind
      have hsb : 0 < x.a * y.b + x.b * y.a := by
        have t1 : 0 < x.a * y.b := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.a) (by grind : (0:Rat) < -y.b); grind
        have t2 : 0 < x.b * y.a := Rat.mul_pos hxb_pos hya_pos
        grind
      have hnx : norm x < 0 := by show x.a * x.a - 2 * (x.b * x.b) < 0; grind
      have hny : 0 < norm y := by show 0 < y.a * y.a - 2 * (y.b * y.b); grind
      have hnxy : norm (x * y) < 0 := by
        rw [norm_mul]
        have := Rat.mul_pos (by grind : 0 < -norm x) hny
        grind
      refine Or.inr (Or.inr ⟨hsa, by grind, ?_⟩)
      have hraw : (x.a * y.a + 2 * (x.b * y.b)) * (x.a * y.a + 2 * (x.b * y.b))
          - 2 * ((x.a * y.b + x.b * y.a) * (x.a * y.b + x.b * y.a)) < 0 := hnxy
      grind
    · -- branch3 + branch3 → branch2
      obtain ⟨hxa, hxb, hxsq⟩ := hx3
      obtain ⟨hya, hyb, hysq⟩ := hy3
      have hxb_pos : 0 < x.b := by
        rcases Rat.le_iff_lt_or_eq.mp hxb with h' | h'
        · exact h'
        · exfalso; have hz : x.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ x.a * x.a := sq_nonneg x.a
          rw [hz] at hxsq; grind
      have hyb_pos : 0 < y.b := by
        rcases Rat.le_iff_lt_or_eq.mp hyb with h' | h'
        · exact h'
        · exfalso; have hz : y.b = 0 := h'.symm
          have hnn : (0 : Rat) ≤ y.a * y.a := sq_nonneg y.a
          rw [hz] at hysq; grind
      show Pos (⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩ : QS)
      have hsa : 0 < x.a * y.a + 2 * (x.b * y.b) := by
        have t1 : 0 < x.a * y.a := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.a) (by grind : (0:Rat) < -y.a); grind
        have t2 : 0 < x.b * y.b := Rat.mul_pos hxb_pos hyb_pos
        grind
      have hsb : x.a * y.b + x.b * y.a < 0 := by
        have t1 : x.a * y.b < 0 := by
          have := Rat.mul_pos (by grind : (0:Rat) < -x.a) hyb_pos; grind
        have t2 : x.b * y.a < 0 := by
          have := Rat.mul_pos hxb_pos (by grind : (0:Rat) < -y.a); grind
        grind
      have hnx : norm x < 0 := by show x.a * x.a - 2 * (x.b * x.b) < 0; grind
      have hny : norm y < 0 := by show y.a * y.a - 2 * (y.b * y.b) < 0; grind
      have hnxy : 0 < norm (x * y) := by
        rw [norm_mul]
        have := Rat.mul_pos (by grind : 0 < -norm x) (by grind : 0 < -norm y)
        grind
      refine Or.inr (Or.inl ⟨Rat.le_of_lt hsa, hsb, ?_⟩)
      have hraw : 0 < (x.a * y.a + 2 * (x.b * y.b)) * (x.a * y.a + 2 * (x.b * y.b))
          - 2 * ((x.a * y.b + x.b * y.a) * (x.a * y.b + x.b * y.a)) := hnxy
      grind

end QS

end PrimitiveReflexivity.OrderObstruction

#print axioms PrimitiveReflexivity.OrderObstruction.retraction_is_identity
#print axioms PrimitiveReflexivity.OrderObstruction.no_retraction_if_gap
#print axioms PrimitiveReflexivity.OrderObstruction.no_sqrt_two_nat
#print axioms PrimitiveReflexivity.OrderObstruction.no_order_retraction_of_sqrt_two
#print axioms PrimitiveReflexivity.OrderObstruction.rat_no_sqrt_two
#print axioms PrimitiveReflexivity.OrderObstruction.witness_rat
#print axioms PrimitiveReflexivity.OrderObstruction.density_needed
#print axioms PrimitiveReflexivity.OrderObstruction.retract_needed
#print axioms PrimitiveReflexivity.OrderObstruction.no_order_retraction_rat
#print axioms PrimitiveReflexivity.OrderObstruction.no_retraction_local
#print axioms PrimitiveReflexivity.OrderObstruction.QS.s_mul_s
#print axioms PrimitiveReflexivity.OrderObstruction.QS.trich_s
#print axioms PrimitiveReflexivity.OrderObstruction.QS.add_assoc
#print axioms PrimitiveReflexivity.OrderObstruction.QS.add_comm
#print axioms PrimitiveReflexivity.OrderObstruction.QS.zero_add
#print axioms PrimitiveReflexivity.OrderObstruction.QS.add_zero
#print axioms PrimitiveReflexivity.OrderObstruction.QS.add_left_neg
#print axioms PrimitiveReflexivity.OrderObstruction.QS.sub_eq_add_neg
#print axioms PrimitiveReflexivity.OrderObstruction.QS.norm_eq_zero_iff
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mul_inv_cancel
#print axioms PrimitiveReflexivity.OrderObstruction.QS.no_order_retraction_Qsqrt2
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mono_needed
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mul_assoc
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mul_comm
#print axioms PrimitiveReflexivity.OrderObstruction.QS.one_mul
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mul_one
#print axioms PrimitiveReflexivity.OrderObstruction.QS.left_distrib
#print axioms PrimitiveReflexivity.OrderObstruction.QS.right_distrib
#print axioms PrimitiveReflexivity.OrderObstruction.QS.add_lt_add_left
#print axioms PrimitiveReflexivity.OrderObstruction.QS.pos_trichotomy
#print axioms PrimitiveReflexivity.OrderObstruction.QS.sq_le_sq_of_nonneg
#print axioms PrimitiveReflexivity.OrderObstruction.QS.sq_lt_sq_of_nonneg
#print axioms PrimitiveReflexivity.OrderObstruction.QS.le_of_sq_le
#print axioms PrimitiveReflexivity.OrderObstruction.QS.sqLe_add
#print axioms PrimitiveReflexivity.OrderObstruction.QS.dominance_mul_lt
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mixed_not_neg
#print axioms PrimitiveReflexivity.OrderObstruction.QS.sqLe_add2
#print axioms PrimitiveReflexivity.OrderObstruction.QS.pos_add_branch1_left
#print axioms PrimitiveReflexivity.OrderObstruction.QS.pos_add
#print axioms PrimitiveReflexivity.OrderObstruction.QS.trichotomy
#print axioms PrimitiveReflexivity.OrderObstruction.QS.transitivity
#print axioms PrimitiveReflexivity.OrderObstruction.QS.norm_mul
#print axioms PrimitiveReflexivity.OrderObstruction.QS.pos_scale
#print axioms PrimitiveReflexivity.OrderObstruction.QS.pos_s_mul
#print axioms PrimitiveReflexivity.OrderObstruction.QS.pos_mul_branch1_left
#print axioms PrimitiveReflexivity.OrderObstruction.QS.mul_pos
