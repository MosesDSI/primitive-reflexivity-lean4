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
