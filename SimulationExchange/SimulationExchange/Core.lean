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
-/

attribute [local instance] Lean.Grind.Ring.intCast
open Lean.Grind

namespace SimulationExchange

/-! ## §0  Non-squares -/

/-- `d` is not the square of any natural number. -/
def NonSquare (d : Nat) : Prop := ∀ r : Nat, r * r ≠ d

/-- Every natural number lies between two consecutive squares. -/
theorem exists_floor_sqrt (d : Nat) : ∃ a : Nat, a * a ≤ d ∧ d < (a + 1) * (a + 1) := by
  induction d with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ d ih =>
    obtain ⟨a, h1, h2⟩ := ih
    by_cases h : d + 1 < (a + 1) * (a + 1)
    · exact ⟨a, by omega, h⟩
    · refine ⟨a + 1, by omega, ?_⟩
      have : (a + 1 + 1) * (a + 1 + 1) = (a + 1) * (a + 1) + 2 * a + 3 := by grind
      omega

/-- A number strictly between two consecutive squares is a non-square. -/
theorem nonSquare_of_between (d a : Nat) (h1 : a * a < d) (h2 : d < (a + 1) * (a + 1)) :
    NonSquare d := by
  intro r hr
  by_cases hra : r ≤ a
  · have := Nat.mul_self_le_mul_self hra
    omega
  · have : a + 1 ≤ r := by omega
    have := Nat.mul_self_le_mul_self this
    omega

/-! ## §1  The descent: the integer core of faithfulness -/

/-- **Descent.** If `d` is a non-square, then `t·t·d = k·k` forces `t = 0`.
    This generalizes the paper's Theorem 7.4 (the case `d = 2`) to every
    non-square, by the classical descent `(t, k) ↦ (k − a·t, d·t − a·k)`
    with `a = ⌊√d⌋`, which strictly decreases `t`. -/
theorem descent {d : Nat} (hd : NonSquare d) (t k : Nat) (h : t * t * d = k * k) : t = 0 := by
  rcases Nat.eq_zero_or_pos t with h0 | ht
  · exact h0
  exfalso
  obtain ⟨a, ha1, ha2⟩ := exists_floor_sqrt d
  have ha : a * a < d := Nat.lt_of_le_of_ne ha1 (hd a)
  have htt : 0 < t * t := Nat.mul_pos ht ht
  -- a·t < k
  have hlo : a * t < k := by
    have : a * a * (t * t) < d * (t * t) := Nat.mul_lt_mul_of_pos_right ha htt
    have : (a * t) * (a * t) < k * k := by grind
    exact Nat.mul_self_lt_mul_self_iff.mp this
  -- k < (a+1)·t
  have hhi : k < (a + 1) * t := by
    have : d * (t * t) < (a + 1) * (a + 1) * (t * t) := Nat.mul_lt_mul_of_pos_right ha2 htt
    have : k * k < ((a + 1) * t) * ((a + 1) * t) := by grind
    exact Nat.mul_self_lt_mul_self_iff.mp this
  -- a·k < d·t
  have hak : a * k < d * t := by
    have : a * t * k < k * k := Nat.mul_lt_mul_of_pos_right hlo (by omega)
    have : (a * k) * t < (d * t) * t := by grind
    exact Nat.lt_of_mul_lt_mul_right this
  -- the descended pair
  obtain ⟨t', ht'⟩ : ∃ t', t' + a * t = k := ⟨k - a * t, by omega⟩
  obtain ⟨k', hk'⟩ : ∃ k', k' + a * k = d * t := ⟨d * t - a * k, by omega⟩
  have hsq : t' * t' * d = k' * k' := by grind
  have hpos : 0 < t' := by omega
  have hlt : t' < t := by
    have : (a + 1) * t = a * t + t := Nat.succ_mul a t
    omega
  have := descent hd t' k' hsq
  omega
termination_by t

/-- The descent over the integers. -/
theorem descent_int {d : Nat} (hd : NonSquare d) (x y : Int)
    (h : x * x * (d : Int) = y * y) : x = 0 := by
  have h' := congrArg Int.natAbs h
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at h'
  exact Int.natAbs_eq_zero.mp (descent hd x.natAbs y.natAbs h')

/-- `x·x = 0` forces `x = 0` over the integers. -/
theorem int_mul_self_eq_zero {x : Int} (h : x * x = 0) : x = 0 := by
  rcases Int.mul_eq_zero.mp h with h | h <;> exact h

/-! ## §2  Characteristic-zero transfer -/

/-- In a ring of characteristic 0, an integer that becomes 0 was already 0. -/
theorem int_eq_zero_of_cast {R : Type} [CommRing R] [IsCharP R 0] (x : Int)
    (h : (Int.cast x : R) = 0) : x = 0 := by
  have := (IsCharP.intCast_eq_zero_iff (α := R) 0 x).mp h
  simpa using this

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
  fun h => absurd (h 1 2 rfl) (by decide)

/-- The norm core needs `NonSquare (d₁·d₂)`: `(d₁,d₂) = (2,8)`, `A = 1`. -/
theorem normForm_needs_product : normForm 2 8 1 2 0 = 0 := by decide
/-- The norm core needs `NonSquare d₁`: `(d₁,d₂) = (4,2)`, `B = 1`. -/
theorem normForm_needs_first : normForm 4 2 0 1 (-2) = 0 := by decide
/-- The norm core needs `NonSquare d₂`: `(d₁,d₂) = (2,4)`, `A = 1`. -/
theorem normForm_needs_second : normForm 2 4 1 0 2 = 0 := by decide

/-! ## §6  Satisfiability: the hypotheses hold for real instructures -/

theorem nonSquare_2 : NonSquare 2 := nonSquare_of_between 2 1 (by decide) (by decide)
theorem nonSquare_3 : NonSquare 3 := nonSquare_of_between 3 1 (by decide) (by decide)
theorem nonSquare_6 : NonSquare (2 * 3) := nonSquare_of_between 6 2 (by decide) (by decide)
theorem nonSquare_30 : NonSquare 30 := nonSquare_of_between 30 5 (by decide) (by decide)
theorem nonSquare_33 : NonSquare 33 := nonSquare_of_between 33 5 (by decide) (by decide)
theorem nonSquare_990 : NonSquare (30 * 33) := nonSquare_of_between 990 31 (by decide) (by decide)

end SimulationExchange
