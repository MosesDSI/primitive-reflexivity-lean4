/-
  Simulation_Exchange.lean  —  bare Lean 4 (no Mathlib)

  Two incommensurable walkers, rendered from one shared carrier tick n:
      walker 1 at phase  n·s − k₁,   walker 2 at phase  n·t − k₂,
  where s·s = d₁ and t·t = d₂ in any commutative ring R of characteristic 0
  (for R = ℝ, s = √d₁, t = √d₂ and kᵢ = ⌊n·√dᵢ⌋ give the trap's phases).

  Theorem A (contained):   walker 1's phase determines the carrier tick,
                           so it determines walker 2's phase.
  Theorem B (not direct):  at no tick n ≥ 1 is walker 2's phase a rational
                           affine function of walker 1's phase.

  Zero-axiom status (see AGENTS.md): §0–§2 and §5–§6 are proved without
  axioms and without `simp`/`omega`/`decide`/`by_cases`/`grind`, using
  `ZeroNat`, `ZeroGrind` and ZeroInt's proved lemmas. §3–§4 are rewritten in
  the next increment.
-/

import SimulationExchange.ZeroNat
import SimulationExchange.ZeroGrind

set_option genInjectivity false

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange

/-! ## §0  Non-squares -/

/-- `d` is not the square of any natural number. -/
def NonSquare (d : Nat) : Prop := ∀ r : Nat, r * r ≠ d

/-- Every natural number lies between two consecutive squares.
    (Peano induction: from `a² ≤ d < (a+1)²`, either `d + 1 < (a+1)²` keeps
    `a`, or `d + 1 = (a+1)²` moves to `a + 1`.) -/
theorem exists_floor_sqrt : (d : Nat) → ∃ a : Nat, a * a ≤ d ∧ d < (a + 1) * (a + 1)
  | 0 => ⟨0, Nat.le_refl 0, Nat.zero_lt_one⟩
  | d + 1 => by
    obtain ⟨a, h₁, h₂⟩ := exists_floor_sqrt d
    cases Nat.lt_or_eq_of_le (h₂ : d + 1 ≤ (a + 1) * (a + 1)) with
    | inl hlt => exact ⟨a, Nat.le_succ_of_le h₁, hlt⟩
    | inr heq =>
      exact ⟨a + 1, Nat.le_of_eq (Eq.symm heq),
        Nat.lt_of_le_of_lt (Nat.le_of_eq heq)
          (ZeroNat.mul_self_lt_of_lt (Nat.lt_succ_self (a + 1)))⟩

/-- A number strictly between two consecutive squares is a non-square.
    (Case split `r ≤ a` or `a + 1 ≤ r`; squaring is monotone.) -/
theorem nonSquare_of_between (d a : Nat) (h1 : a * a < d) (h2 : d < (a + 1) * (a + 1)) :
    NonSquare d :=
  fun r hr =>
    match Nat.lt_or_ge r (a + 1) with
    | Or.inl hlt =>
      Nat.lt_irrefl d
        (Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.le_of_eq (Eq.symm hr))
            (ZeroNat.mul_self_le_mul_self (Nat.le_of_lt_succ hlt)))
          h1)
    | Or.inr hge =>
      Nat.lt_irrefl d
        (Nat.lt_of_lt_of_le h2
          (Nat.le_trans (ZeroNat.mul_self_le_mul_self hge) (Nat.le_of_eq hr)))

/-! ## §1  The descent: the integer core of faithfulness -/

open SimulationExchange.ZeroInt (nat_add_mul nat_mul_assoc nat_mul_left_comm nat_eq_of_sum)
open SimulationExchange.ZeroNat
  (mul_lt_mul_right_of_pos mul_pos' mul_mul_self lt_of_mul_self_lt_mul_self)

/-- **One descent step.** If `d` is not a square, `n > 0` and `j² = n²d`,
    there is a smaller positive `n'` with some `j'² = n'²d`. With
    `r = ⌊√d⌋`: `n' = j − r n` and `j' = d n − r j`, introduced as witnesses
    (`r n + n' = j`, `r j + j' = d n`), never by Nat subtraction. The two
    cross relations `j'·n = n'·j` and `j'·j = n'·(dn)` come from cancelling a
    common summand (`nat_eq_of_sum`); together they give `n·j'² = n·(n'²d)`. -/
theorem descent_step {d n j : Nat} (hd : NonSquare d) (hn : 0 < n)
    (hj : j * j = n * n * d) :
    ∃ n' j' : Nat, 0 < n' ∧ n' < n ∧ j' * j' = n' * n' * d := by
  obtain ⟨r, hr₁, hr₂⟩ := exists_floor_sqrt d
  have hr : r * r < d := Nat.lt_of_le_of_ne hr₁ (hd r)
  have hd₀ : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le (r * r)) hr
  have hnn : 0 < n * n := mul_pos' hn hn
  have hjj : 0 < j * j :=
    Nat.lt_of_lt_of_le (mul_pos' hnn hd₀) (Nat.le_of_eq (Eq.symm hj))
  have hjd : j * j = d * (n * n) := Eq.trans hj (Nat.mul_comm (n * n) d)
  have hlo : r * n < j :=
    lt_of_mul_self_lt_mul_self
      (Nat.lt_of_le_of_lt (Nat.le_of_eq (mul_mul_self r n))
        (Nat.lt_of_lt_of_le (mul_lt_mul_right_of_pos hr hnn) (Nat.le_of_eq (Eq.symm hjd))))
  have hhi : j < (r + 1) * n :=
    lt_of_mul_self_lt_mul_self
      (Nat.lt_of_le_of_lt (Nat.le_of_eq hjd)
        (Nat.lt_of_lt_of_le (mul_lt_mul_right_of_pos hr₂ hnn)
          (Nat.le_of_eq (Eq.symm (mul_mul_self (r + 1) n)))))
  obtain ⟨n', hA⟩ := Nat.le.dest (Nat.le_of_lt hlo)
  have hn'pos : 0 < n' :=
    Nat.lt_of_add_lt_add_left
      (Nat.lt_of_lt_of_le hlo (Nat.le_of_eq (Eq.symm hA)) : r * n + 0 < r * n + n')
  have e_r1n : (r + 1) * n = r * n + n :=
    Eq.trans (nat_add_mul r 1 n) (congrArg (fun t => r * n + t) (Nat.one_mul n))
  have hn'lt : n' < n :=
    Nat.lt_of_add_lt_add_left
      (Nat.lt_of_le_of_lt (Nat.le_of_eq hA)
        (Nat.lt_of_lt_of_le hhi (Nat.le_of_eq e_r1n)) : r * n + n' < r * n + n)
  have e_dn : d * (j * j) = (d * n) * (d * n) :=
    Eq.trans (congrArg (fun t => d * t) hjd)
      (Eq.trans (Eq.symm (nat_mul_assoc d d (n * n))) (Eq.symm (mul_mul_self d n)))
  have hrj : r * j < d * n :=
    lt_of_mul_self_lt_mul_self
      (Nat.lt_of_le_of_lt (Nat.le_of_eq (mul_mul_self r j))
        (Nat.lt_of_lt_of_le (mul_lt_mul_right_of_pos hr hjj) (Nat.le_of_eq e_dn)))
  obtain ⟨j', hB⟩ := Nat.le.dest (Nat.le_of_lt hrj)
  have e₁ : d * n * n = n * n * d :=
    Eq.trans (nat_mul_assoc d n n) (Nat.mul_comm d (n * n))
  have e₂ : r * j * n = r * n * j :=
    Eq.trans (nat_mul_assoc r j n)
      (Eq.trans (congrArg (fun t => r * t) (Nat.mul_comm j n))
        (Eq.symm (nat_mul_assoc r n j)))
  have hD : j' * n = n' * j :=
    nat_eq_of_sum (K := r * n * j)
      (Eq.trans e₁ (Eq.symm hj) : d * n * n = j * j)
      (Eq.trans (congrArg (fun t => t * n) (Eq.symm hB))
        (Eq.trans (nat_add_mul (r * j) j' n) (congrArg (fun t => t + j' * n) e₂)))
      (Eq.trans (congrArg (fun t => t * j) (Eq.symm hA)) (nat_add_mul (r * n) n' j))
  have e₃ : r * j * j = r * n * (d * n) :=
    Eq.trans (nat_mul_assoc r j j)
      (Eq.trans
        (congrArg (fun t => r * t)
          (Eq.trans hj
            (Eq.trans (nat_mul_assoc n n d) (congrArg (fun t => n * t) (Nat.mul_comm n d)))))
        (Eq.symm (nat_mul_assoc r n (d * n))))
  have hE : j' * j = n' * (d * n) :=
    nat_eq_of_sum (K := r * n * (d * n))
      (Nat.mul_comm (d * n) j)
      (Eq.trans (congrArg (fun t => t * j) (Eq.symm hB))
        (Eq.trans (nat_add_mul (r * j) j' j) (congrArg (fun t => t + j' * j) e₃)))
      (Eq.trans (congrArg (fun t => t * (d * n)) (Eq.symm hA)) (nat_add_mul (r * n) n' (d * n)))
  have hfin : n * (j' * j') = n * (n' * n' * d) :=
    Eq.trans (Nat.mul_comm n (j' * j'))
      (Eq.trans (nat_mul_assoc j' j' n)
        (Eq.trans (congrArg (fun t => j' * t) hD)
          (Eq.trans (nat_mul_left_comm j' n' j)
            (Eq.trans (congrArg (fun t => n' * t) hE)
              (Eq.trans (Eq.symm (nat_mul_assoc n' n' (d * n)))
                (Eq.trans (Eq.symm (nat_mul_assoc (n' * n') d n))
                  (Nat.mul_comm (n' * n' * d) n)))))))
  exact ⟨n', j', hn'pos, hn'lt, Nat.eq_of_mul_eq_mul_left hn hfin⟩

/-- Strong induction by hand (ordinary Peano induction on a bound `N`): no
    positive `n < N` has a solution `j² = n²d`. -/
theorem no_square_multiple_aux {d : Nat} (hd : NonSquare d) :
    ∀ N n : Nat, n < N → 0 < n → ∀ j : Nat, j * j = n * n * d → False
  | 0, n, h, _, _, _ => absurd h (Nat.not_lt_zero n)
  | N + 1, _n, h, hn, _j, hj =>
    match descent_step hd hn hj with
    | ⟨n', j', hpos, hlt, hj'⟩ =>
      no_square_multiple_aux hd N n'
        (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ h)) hpos j' hj'

/-- If `d` is not a perfect square and `n > 0`, no `j` has `j² = n²d`. -/
theorem no_square_multiple {d n : Nat} (hd : NonSquare d) (hn : 0 < n) :
    ∀ j : Nat, j * j ≠ n * n * d :=
  fun j hj => no_square_multiple_aux hd (n + 1) n (Nat.lt_succ_self n) hn j hj

/-- **Descent.** If `d` is a non-square, then `t·t·d = k·k` forces `t = 0`.
    This generalizes the paper's Theorem 7.4 (the case `d = 2`) to every
    non-square, by the classical descent `(t, k) ↦ (k − a·t, d·t − a·k)`
    with `a = ⌊√d⌋`, which strictly decreases `t` (`descent_step`). -/
theorem descent {d : Nat} (hd : NonSquare d) (t k : Nat) (h : t * t * d = k * k) : t = 0 :=
  match t, h with
  | 0, _ => rfl
  | s + 1, h => absurd (Eq.symm h) (no_square_multiple hd (Nat.zero_lt_succ s) k)

/-- Every integer squares to a natural square: `x·x = m·m` with `m = |x|`,
    and `m = 0` only for `x = 0`. (By the two constructors of `Int`; both
    products compute to `Int.ofNat` by definition.) -/
theorem int_mul_self_natSq : ∀ x : Int, ∃ m : Nat, x * x = Int.ofNat (m * m) ∧ (m = 0 → x = 0)
  | Int.ofNat p => ⟨p, rfl, fun h => congrArg Int.ofNat h⟩
  | Int.negSucc p => ⟨p + 1, rfl, fun h => Nat.noConfusion h⟩

/-- The descent over the integers. -/
theorem descent_int {d : Nat} (hd : NonSquare d) (x y : Int)
    (h : x * x * (d : Int) = y * y) : x = 0 := by
  obtain ⟨m, hx, hm⟩ := int_mul_self_natSq x
  obtain ⟨l, hy, _⟩ := int_mul_self_natSq y
  rw [hx, hy] at h
  have h' : Int.ofNat (m * m * d) = Int.ofNat (l * l) := h
  exact hm (descent hd m l (Int.ofNat.inj h'))

/-- `x·x = 0` forces `x = 0` over the integers. -/
theorem int_mul_self_eq_zero {x : Int} (h : x * x = 0) : x = 0 :=
  match int_mul_self_natSq x with
  | ⟨_m, hx, hm⟩ =>
    hm (ZeroNat.mul_self_eq_zero
      (Int.ofNat.inj (Eq.trans (Eq.symm hx) h : Int.ofNat (_m * _m) = Int.ofNat 0)))

/-! ## §2  Characteristic-zero transfer -/

/-- In a ring of characteristic 0, an integer that becomes 0 was already 0.
    (Proof in `ZeroGrind`, read through `IsCharP`'s single field.) -/
theorem int_eq_zero_of_cast {R : Type} [CommRing R] [IsCharP R 0] (x : Int)
    (h : (Int.cast x : R) = 0) : x = 0 :=
  ZeroGrind.int_eq_zero_of_cast x h

/-! ## §3  Theorem A — faithfulness: the information is contained -/

/-- **Theorem A (faithfulness, simulation condition S2).**
    Let `s·s = d` with `d` a non-square, in a commutative ring of
    characteristic 0. If ticks `n` and `m` render walker 1 to the same phase
    — i.e. their displacement `(n − m)·s` is an integer `j` — then `n = m`.
    For `R = ℝ`, `s = √d`, this is exactly:
    `frac(n√d) = frac(m√d) → n = m`  (take `j = ⌊n√d⌋ − ⌊m√d⌋`). -/
theorem faithful {R : Type} [CommRing R] [IsCharP R 0]
    {d : Nat} (hd : NonSquare d) (s : R) (hs : s * s = Int.cast (d : Int))
    (n m : Int) (j : Int) (h : Int.cast (n - m) * s = (Int.cast j : R)) : n = m := by
  have hR : (Int.cast ((n - m) * (n - m) * (d : Int) - j * j) : R) = 0 := by
    grind
  have hZ := int_eq_zero_of_cast _ hR
  have : (n - m) * (n - m) * (d : Int) = j * j := by omega
  have := descent_int hd (n - m) j this
  omega

/-- **Corollary A′ (walker 1 carries walker 2).** Whatever walker 1 cannot
    tell apart, walker 2 cannot tell apart either: a phase coincidence of
    walker 1 between two ticks forces a phase coincidence of walker 2.
    Equivalently, walker 2's rendered phase is a function of walker 1's,
    defined through the carrier tick. Only walker 1's non-squareness is used. -/
theorem walker1_determines_walker2 {R : Type} [CommRing R] [IsCharP R 0]
    {d₁ : Nat} (hd₁ : NonSquare d₁) (s t : R) (hs : s * s = Int.cast (d₁ : Int))
    (n m j : Int) (h : Int.cast (n - m) * s = (Int.cast j : R)) :
    ∃ j₂ : Int, Int.cast (n - m) * t = (Int.cast j₂ : R) := by
  have hnm := faithful hd₁ s hs n m j h
  refine ⟨0, ?_⟩
  subst hnm
  grind

/-! ## §4  Theorem B — the information is not directly available -/

/-- The norm of `C + B·s − A·t`: the product of its four sign-conjugates,
    written in integers. -/
def normForm (d₁ d₂ A B C : Int) : Int :=
  (C * C + A * A * d₂ - B * B * d₁) * (C * C + A * A * d₂ - B * B * d₁) - 4 * A * A * C * C * d₂

/-- The norm identity, valid in every commutative ring in which `s·s = d₁`,
    `t·t = d₂` (any choice of signs, so it holds in every orientation). -/
theorem norm_identity {R : Type} [CommRing R] (s t : R) (d₁ d₂ A B C : Int)
    (hs : s * s = Int.cast d₁) (ht : t * t = Int.cast d₂) :
    (Int.cast C + Int.cast B * s - Int.cast A * t) * (Int.cast C - Int.cast B * s - Int.cast A * t)
      * (Int.cast C + Int.cast B * s + Int.cast A * t) * (Int.cast C - Int.cast B * s + Int.cast A * t)
      = (Int.cast (normForm d₁ d₂ A B C) : R) := by
  unfold normForm
  grind

/-- **Integer core, walker-2 coefficient.** If `d₂` and `d₁·d₂` are
    non-squares, a vanishing norm forces the `t`-coefficient `A` to vanish.
    (`d₁` itself is not needed for this conclusion.) -/
theorem normForm_A_eq_zero {d₁ d₂ : Nat} (h₂ : NonSquare d₂) (h₁₂ : NonSquare (d₁ * d₂))
    (A B C : Int) (h : normForm d₁ d₂ A B C = 0) : A = 0 := by
  unfold normForm at h
  -- u² = d₂·(2AC)²  ⟹  2AC = 0
  have h2AC : (2 * A * C) * (2 * A * C) * (d₂ : Int)
      = (C * C + A * A * d₂ - B * B * d₁) * (C * C + A * A * d₂ - B * B * d₁) := by grind
  have hz := descent_int h₂ _ _ h2AC
  have hu : (C * C + A * A * d₂ - B * B * d₁) * (C * C + A * A * d₂ - B * B * d₁) = 0 := by
    rw [← h2AC, hz]; simp
  have hu0 : C * C + A * A * d₂ - B * B * d₁ = 0 := int_mul_self_eq_zero hu
  have hd₂ : (d₂ : Int) ≠ 0 := by
    intro h0; exact h₂ 0 (by omega)
  have hAC : A = 0 ∨ C = 0 := by
    have : A * C = 0 := by grind
    exact Int.mul_eq_zero.mp this
  rcases hAC with hA | hC
  · exact hA
  · -- C = 0:  A²·d₂ = B²·d₁  ⟹  (A·d₂)² = B²·(d₁d₂)  ⟹  B = 0  ⟹  A = 0
    subst hC
    have hB := descent_int h₁₂ B (A * d₂) (by push_cast; grind)
    subst hB
    have : A * A * (d₂ : Int) = 0 := by grind
    have hAA : A * A = 0 := by
      rcases Int.mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hd₂
    exact int_mul_self_eq_zero hAA

/-- **Integer core, full.** Under the whole independence condition
    (`d₁`, `d₂`, `d₁·d₂` all non-squares) the norm vanishes only at `0`. -/
theorem normForm_eq_zero {d₁ d₂ : Nat} (h₁ : NonSquare d₁) (h₂ : NonSquare d₂)
    (h₁₂ : NonSquare (d₁ * d₂)) (A B C : Int) (h : normForm d₁ d₂ A B C = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hA := normForm_A_eq_zero h₂ h₁₂ A B C h
  subst hA
  unfold normForm at h
  -- with A = 0 the norm is (C² − B²d₁)², so C² = B²·d₁  ⟹  B = 0  ⟹  C = 0
  have hu : (C * C - B * B * d₁) * (C * C - B * B * d₁) = 0 := by grind
  have hu0 := int_mul_self_eq_zero hu
  have hB := descent_int h₁ B C (by grind)
  subst hB
  have : C * C = 0 := by grind
  exact ⟨rfl, rfl, int_mul_self_eq_zero this⟩

/-- Transfer of a vanishing combination `C + B·s − A·t = 0` in `R` to a
    vanishing norm in `ℤ`, through the norm identity and characteristic 0. -/
theorem normForm_eq_zero_of_vanishing {R : Type} [CommRing R] [IsCharP R 0]
    {d₁ d₂ : Nat} (s t : R) (hs : s * s = Int.cast (d₁ : Int)) (ht : t * t = Int.cast (d₂ : Int))
    (A B C : Int) (h : Int.cast C + Int.cast B * s - Int.cast A * t = (0 : R)) :
    normForm d₁ d₂ A B C = 0 := by
  have hid := norm_identity s t d₁ d₂ A B C hs ht
  rw [h] at hid
  have hcast : (Int.cast (normForm d₁ d₂ A B C) : R) = 0 := by
    rw [← hid]; grind
  exact int_eq_zero_of_cast _ hcast

/-- **Linear independence of `1, s, t`.** In any commutative ring of
    characteristic 0 with `s·s = d₁`, `t·t = d₂` and the independence
    condition, `C + B·s − A·t = 0` forces `A = B = C = 0`. For `R = ℝ` this is
    `√d₂ ∉ ℚ(√d₁)` together with the irrationality of `√d₁`. -/
theorem independent {R : Type} [CommRing R] [IsCharP R 0]
    {d₁ d₂ : Nat} (h₁ : NonSquare d₁) (h₂ : NonSquare d₂) (h₁₂ : NonSquare (d₁ * d₂))
    (s t : R) (hs : s * s = Int.cast (d₁ : Int)) (ht : t * t = Int.cast (d₂ : Int))
    (A B C : Int) (h : Int.cast C + Int.cast B * s - Int.cast A * t = (0 : R)) :
    A = 0 ∧ B = 0 ∧ C = 0 :=
  normForm_eq_zero h₁ h₂ h₁₂ A B C (normForm_eq_zero_of_vanishing s t hs ht A B C h)

/-- **Theorem B (no direct rule).** At no tick `n ≥ 1` is walker 2's phase
    `θ₂ = n·t − k₂` a rational affine function `θ₂ = (u/v)·θ₁ + w/v` of
    walker 1's phase `θ₁ = n·s − k₁`, for any integer offsets `k₁, k₂`
    (in particular the floors) and any rational rule with `v ≥ 1`.
    Uses exactly `NonSquare d₂` and `NonSquare (d₁·d₂)`; §5 shows each is needed. -/
theorem no_direct_rule {R : Type} [CommRing R] [IsCharP R 0]
    {d₁ d₂ : Nat} (h₂ : NonSquare d₂) (h₁₂ : NonSquare (d₁ * d₂))
    (s t : R) (hs : s * s = Int.cast (d₁ : Int)) (ht : t * t = Int.cast (d₂ : Int))
    (n v u w k₁ k₂ : Int) (hn : 1 ≤ n) (hv : 1 ≤ v)
    (θ₁ θ₂ : R) (e₁ : θ₁ = Int.cast n * s - Int.cast k₁) (e₂ : θ₂ = Int.cast n * t - Int.cast k₂)
    (rule : Int.cast v * θ₂ = Int.cast u * θ₁ + (Int.cast w : R)) : False := by
  have h0 : Int.cast (v * k₂ - u * k₁ + w) + Int.cast (u * n) * s - Int.cast (v * n) * t = (0 : R) := by
    subst e₁ e₂; grind
  have hA := normForm_A_eq_zero h₂ h₁₂ (v * n) (u * n) (v * k₂ - u * k₁ + w)
    (normForm_eq_zero_of_vanishing s t hs ht _ _ _ h0)
  have : 0 < v * n := Int.mul_pos (by omega) (by omega)
  omega

/-! ## §5  Necessity: every hypothesis does work -/

/-- Theorem A needs `NonSquare d`: for `d = 4`, `t = 1, k = 2` defeats the descent. -/
theorem descent_needs_nonSquare : ¬ (∀ t k : Nat, t * t * 4 = k * k → t = 0) :=
  fun h => Nat.noConfusion (h 1 2 rfl)

/-- The norm core needs `NonSquare (d₁·d₂)`: `(d₁,d₂) = (2,8)`, `A = 1`.
    (Closed integer evaluation, checked by `rfl`.) -/
theorem normForm_needs_product : normForm 2 8 1 2 0 = 0 := rfl
/-- The norm core needs `NonSquare d₁`: `(d₁,d₂) = (4,2)`, `B = 1`. -/
theorem normForm_needs_first : normForm 4 2 0 1 (-2) = 0 := rfl
/-- The norm core needs `NonSquare d₂`: `(d₁,d₂) = (2,4)`, `A = 1`. -/
theorem normForm_needs_second : normForm 2 4 1 0 2 = 0 := rfl

/-! ## §6  Satisfiability: the hypotheses hold for real instructures

Each bound `a² < d < (a+1)²` is a closed `Nat.ble` evaluation
(`Nat.le_of_ble_eq_true rfl`, written in its `n + 1 ≤ m` form). -/

theorem nonSquare_2 : NonSquare 2 :=
  nonSquare_of_between 2 1 (Nat.le_of_ble_eq_true rfl : 1 * 1 + 1 ≤ 2)
    (Nat.le_of_ble_eq_true rfl : 2 + 1 ≤ (1 + 1) * (1 + 1))
theorem nonSquare_3 : NonSquare 3 :=
  nonSquare_of_between 3 1 (Nat.le_of_ble_eq_true rfl : 1 * 1 + 1 ≤ 3)
    (Nat.le_of_ble_eq_true rfl : 3 + 1 ≤ (1 + 1) * (1 + 1))
theorem nonSquare_6 : NonSquare (2 * 3) :=
  nonSquare_of_between 6 2 (Nat.le_of_ble_eq_true rfl : 2 * 2 + 1 ≤ 6)
    (Nat.le_of_ble_eq_true rfl : 6 + 1 ≤ (2 + 1) * (2 + 1))
theorem nonSquare_30 : NonSquare 30 :=
  nonSquare_of_between 30 5 (Nat.le_of_ble_eq_true rfl : 5 * 5 + 1 ≤ 30)
    (Nat.le_of_ble_eq_true rfl : 30 + 1 ≤ (5 + 1) * (5 + 1))
theorem nonSquare_33 : NonSquare 33 :=
  nonSquare_of_between 33 5 (Nat.le_of_ble_eq_true rfl : 5 * 5 + 1 ≤ 33)
    (Nat.le_of_ble_eq_true rfl : 33 + 1 ≤ (5 + 1) * (5 + 1))
theorem nonSquare_990 : NonSquare (30 * 33) :=
  nonSquare_of_between 990 31 (Nat.le_of_ble_eq_true rfl : 31 * 31 + 1 ≤ 990)
    (Nat.le_of_ble_eq_true rfl : 990 + 1 ≤ (31 + 1) * (31 + 1))

end SimulationExchange
