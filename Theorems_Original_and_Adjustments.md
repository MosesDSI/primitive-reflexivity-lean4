# Foundations of Primitive Reflexivity — Theorem Code: Original vs. Verified

This document records the Lean 4 theorem code exactly as originally supplied for formalization
(drawn from "Foundations of Primitive Reflexivity: The Discrete Node-First Ontology, Axis
Incommensurability, and the Phase-Drift Definition of Angles"), and every adjustment made to get
it to build with **zero `sorry`** against the pinned Mathlib revision (`0df444a3`, Lean 4.33.1)
in this project. The final, verified version lives at `PrimitiveReflexivity/Foundations.lean`.

Every adjustment below was required to make the code compile or to close a genuinely incomplete
proof step — none are changes of mathematical content. The theorem statements (the actual claims
being proved) are unchanged from the original; only import paths, lemma names, computability
annotations, and a handful of broken/fragile proof steps were fixed.

---

## 1. As Originally Supplied

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PrimitiveReflexivity

/- SECTION I & II: The Primordial Node Field and Axioms of Reflexivity -/

variable {N : Type}
variable (R : N → N → Prop)

class LocalizedReflexive (R : N → N → Prop) : Prop where
  refl (x : N) : R x x

theorem reflexive_minimality
    (R S : N → N → Prop)
    [instR : LocalizedReflexive R]
    (hS : ∀ x : N, S x x) :
    ∀ x : N, R x x → S x x := by
  intro x _
  exact hS x

theorem reflexive_isomorphism
    {N1 N2 : Type}
    (R1 : N1 → N1 → Prop)
    (R2 : N2 → N2 → Prop)
    [LocalizedReflexive R1]
    [LocalizedReflexive R2]
    (f : N1 ≃ N2) :
    ∀ x : N1, R1 x x ↔ R2 (f x) (f x) := by
  intro x
  constructor
  · intro _
    exact LocalizedReflexive.refl (f x)
  · intro _
    exact LocalizedReflexive.refl x

/- SECTION IV & V: Arithmetic Descent and Prime Per Se Identity -/

def DivSet (p : ℕ) : Set ℕ := { d : ℕ | d ∣ p }

def ArithmeticPerSeIdentity (p : ℕ) : Prop :=
  p > 1 ∧ DivSet p = {1, p}

theorem prime_incompressibility (p : ℕ) :
    Nat.Prime p ↔ ArithmeticPerSeIdentity p := by
  constructor
  · intro hprime
    have hp_gt1 : p > 1 := Nat.Prime.one_lt hprime
    constructor
    · exact hp_gt1
    · ext d
      simp only [DivSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hd_div
        have hd_cases := (Nat.dvd_prime hprime).mp hd_div
        rcases hd_cases with h1 | hp
        · exact Or.inl h1
        · exact Or.inr hp
      · rintro (rfl | rfl)
        · exact one_dvd p
        · exact dvd_rfl
  · rintro ⟨hp_gt1, hdiv_set⟩
    rw [Nat.prime_def_lt']
    refine ⟨hp_gt1, ?_⟩
    intro m hm_gt1 hm_lt_p
    intro hm_div
    have hm_in : m ∈ DivSet p := hm_div
    rw [hdiv_set] at hm_in
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_in
    rcases hm_in with rfl | rfl
    · exact (lt_irrefl 1 (hm_gt1.trans_le (le_refl 1))).elim
    · exact (lt_irrefl m (hm_lt_p.trans_le (le_refl p))).elim

/- SECTION VII: THE DUAL-AXIS INCOMMENSURABILITY THEOREMS -/

def manhattan_step : ℝ := 1 + 1
def diagonal_step : ℝ := Real.sqrt (1 ^ 2 + 1 ^ 2)

lemma diagonal_eq_sqrt_two : diagonal_step = Real.sqrt 2 := by
  unfold diagonal_step
  ring_nf

theorem manhattan_is_rational : ∃ q : ℚ, (q : ℝ) = manhattan_step := by
  use 2
  unfold manhattan_step
  push_cast
  rfl

theorem diagonal_is_irrational : Irrational diagonal_step := by
  rw [diagonal_eq_sqrt_two]
  exact irrational_sqrt_two

theorem no_common_rational_measure : ¬ ∃ q : ℚ, (q : ℝ) = diagonal_step := by
  rw [diagonal_eq_sqrt_two]
  intro h
  rcases h with ⟨q, hq⟩
  have h_irrat := irrational_sqrt_two
  exact h_irrat ⟨q, hq⟩

def delta_gap : ℝ := manhattan_step - diagonal_step

theorem delta_gap_pos : delta_gap > 0 := by
  unfold delta_gap manhattan_step
  rw [diagonal_eq_sqrt_two]
  have h_sqrt2_lt_two : Real.sqrt 2 < 2 := by
    calc Real.sqrt 2
      _ < Real.sqrt 4 := by
        apply Real.sqrt_lt_sqrt
        · norm_num
        · norm_num
      _ = 2 := by
        norm_num
  linarith

theorem two_pi_irrational : Irrational (2 * Real.pi) := by
  have h_pi : Irrational Real.pi := Real.irrational_pi
  have h_two_ne_zero : (2 : ℚ) ≠ 0 := by norm_num
  have h_mul := Irrational.rat_mul h_pi h_two_ne_zero
  exact h_mul

theorem period_incommensurability :
    ¬ ∃ (m n : ℤ), n ≠ 0 ∧ (m : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) := by
  intro h
  rcases h with ⟨m, n, hn_ne_zero, h_eq⟩
  rw [mul_one] at h_eq
  have h_div : (2 * Real.pi) = ((m : ℚ) / (n : ℚ) : ℚ) := by
    apply_fun (fun x => x / (n : ℝ)) at h_eq
    have hn_real_ne : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn_ne_zero
    rw [mul_div_cancel_left₀ (2 * Real.pi) hn_real_ne] at h_eq
    rw [← h_eq]
    push_cast
    rfl
  have h_rational : ∃ q : ℚ, (q : ℝ) = 2 * Real.pi := by
    use (m : ℚ) / (n : ℚ)
    exact h_div.symm
  rcases h_rational with ⟨q, hq⟩
  exact two_pi_irrational ⟨q, hq⟩

/- SECTION IX: THE TRIADIC STATE MANIFOLD & MEDIATOR DEFECT -/

structure TriadicState (n : ℕ) where
  polar_count : ℝ := (n : ℝ)
  axial_mediator : ℝ := Real.sqrt (n : ℝ)
  boundary_potential : ℝ := (n : ℝ) ^ 2

theorem geometric_mean_bridge (n : ℕ) :
    Real.sqrt ((n : ℝ) * ((n : ℝ) ^ 2)) = (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hn_pos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_cube : (n : ℝ) * ((n : ℝ) ^ 2) = (n : ℝ) ^ 3 := by ring
  rw [h_cube]
  have h_split : (n : ℝ) ^ 3 = ((n : ℝ) ^ 2) * (n : ℝ) := by ring
  rw [h_split, Real.sqrt_mul (sq_nonneg (n : ℝ))]
  rw [Real.sqrt_sq hn_pos]

def mediator_defect (n m : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) - Real.sqrt ((n + m : ℕ) : ℝ)

theorem mediator_defect_positive {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    mediator_defect n m > 0 := by
  unfold mediator_defect
  push_cast
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hm_pos
  have h_cross : 0 < 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have h_sq_n : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h_sq_m : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    positivity
  have h_sq_lt : ((Real.sqrt (n + m : ℝ))^2) < ((Real.sqrt n + Real.sqrt m)^2) := by
    rw [Real.sq_sqrt (by linarith)]
    have h_exp : (Real.sqrt n + Real.sqrt m)^2 = n + m + 2 * Real.sqrt n * Real.sqrt m := by
      calc (Real.sqrt n + Real.sqrt m)^2
        _ = (Real.sqrt n)^2 + (Real.sqrt m)^2 + 2 * Real.sqrt n * Real.sqrt m := by ring
        _ = n + m + 2 * Real.sqrt n * Real.sqrt m := by
          rw [Real.sq_sqrt hn_nonneg, Real.sq_sqrt hm_nonneg]
    rw [h_exp]
    linarith
  have h_lt : Real.sqrt (n + m : ℝ) < Real.sqrt n + Real.sqrt m := by
    apply (Real.sqrt_lt_sqrt_iff (by linarith)).mp
    rw [Real.sqrt_sq (by linarith)]
    rw [Real.sqrt_sq (by positivity)]
    exact h_sq_lt
  linarith

theorem equipartition_fixed_point :
    (Real.cos (Real.pi / 4)) ^ 2 = (1 / 2 : ℝ) ∧
    (Real.sin (Real.pi / 4)) ^ 2 = (1 / 2 : ℝ) := by
  constructor
  · rw [Real.cos_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  · rw [Real.sin_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring

end PrimitiveReflexivity
```

---

## 2. Every Adjustment Made, and Why

### 2.1 Import paths (Mathlib file layout has moved since this was written)

| Original import | Verified replacement | Why |
|---|---|---|
| `Mathlib.Data.Real.Irrational` | `Mathlib.NumberTheory.Real.Irrational` **+** `Mathlib.Analysis.Real.Pi.Irrational` | Split into two files at the pinned rev. The first has `Irrational` and `irrational_sqrt_two`; pi-irrationality is no longer pulled in transitively and needs its own import. |
| `Mathlib.Data.Complex.Exponential` | `Mathlib.Analysis.Complex.Exponential` | File moved from `Data` to `Analysis`. |
| `Mathlib.Topology.Instances.Real` | `Mathlib.Topology.Instances.Real.Lemmas` | What was a single file is now a directory; this is its umbrella import. |

Confirmed each by locating the actual file on disk in the cloned `.lake/packages/mathlib` tree before changing the import — not by guessing.

### 2.2 Renamed identifiers

- `Real.irrational_pi` → **`irrational_pi`** — declared at top level in `Mathlib.Analysis.Real.Pi.Irrational`, not inside `namespace Real`.
- `Irrational.rat_mul` → **`Irrational.ratCast_mul`** — signature `(h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x)`. `two_pi_irrational`'s proof was rewritten around this (see 2.5).

### 2.3 Missing `noncomputable` markers

`diagonal_step`, `delta_gap`, and `mediator_defect` all bottom out in `Real.sqrt`, which is
noncomputable (it's built on `Classical.choice`). Lean's compiler rejected all three `def`s for
this reason even though every *proof* about them still type-checked. Added `noncomputable` to
each. (`manhattan_step` and the `TriadicState` structure's default field values did **not** need
this — plain `ℝ` ring operations have computable instances in this Mathlib.)

### 2.4 `manhattan_is_rational` — the closing `rfl` was actually wrong

```lean
-- original
use 2
unfold manhattan_step
push_cast
rfl
```
After `push_cast` the goal is `(2:ℝ) = 1 + 1`. The numeral `2` is *not* definitionally equal to
`1 + 1` in a general semiring (it's built via `OfNat`, not by unfolding addition), so `rfl` was
never going to close this on any Mathlib version — this wasn't an API drift issue. Replaced the
final `rfl` with `norm_num`.

### 2.5 `delta_gap_pos` — the `√4 = 2` step

```lean
-- original
_ = 2 := by
  norm_num
```
`norm_num` cannot evaluate `Real.sqrt` of a literal on its own. Replaced the entire
`h_sqrt2_lt_two` sub-proof with a single call to `Real.sqrt_lt'` (`0 < y → (√x < y ↔ x < y^2)`),
which reduces `√2 < 2` to `2 < 2^2` — closed directly by `norm_num`.

### 2.6 `two_pi_irrational` — rebuilt around the renamed lemma

```lean
-- original
have h_pi : Irrational Real.pi := Real.irrational_pi
have h_two_ne_zero : (2 : ℚ) ≠ 0 := by norm_num
have h_mul := Irrational.rat_mul h_pi h_two_ne_zero
exact h_mul
```
Rewritten to align the real-numeral `2` with the `ℚ`-cast form `ratCast_mul` expects:
```lean
have h2 : (2 : ℝ) * Real.pi = ((2 : ℚ) : ℝ) * Real.pi := by push_cast; ring
rw [h2]
exact irrational_pi.ratCast_mul (by norm_num)
```

### 2.7 `prime_incompressibility` — nonexistent projection

```lean
-- original
· exact (lt_irrefl 1 (hm_gt1.trans_le (le_refl 1))).elim
· exact (lt_irrefl m (hm_lt_p.trans_le (le_refl p))).elim
```
`hm_gt1.trans_le` assumes a `Nat.le.trans_le` field/projection that doesn't exist in the
environment. Both branches are pure arithmetic contradictions once `m` is substituted by `rfl`
(`2 ≤ 1` in one branch, `p < p` in the other) — replaced both with `omega`.

### 2.8 `mediator_defect_positive` — a genuinely fragile step, not just a rename

```lean
-- original h_lt proof
apply (Real.sqrt_lt_sqrt_iff (by linarith)).mp
rw [Real.sqrt_sq (by linarith)]
rw [Real.sqrt_sq (by positivity)]
exact h_sq_lt
```
`Real.sqrt_lt_sqrt_iff` requires **both** sides of the goal to be `Real.sqrt` of something. The
actual goal at that point is `√(n+m) < √n + √m` — the right side is a *sum*, not a single sqrt
application. `apply`'s unifier didn't reject this outright; it silently deferred a metavariable
and produced a nonsensical downstream subgoal (`⊢ √(n+m) < 0`) that no tactic could close. This
was diagnosed by reading the actual proof-state dump, not just re-running the same tactic.

Rewritten from scratch using `Real.sqrt_lt'` directly against an explicit algebraic identity:
```lean
have h_exp : (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ^ 2
    = (n : ℝ) + (m : ℝ) + 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
  have h1 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
  have h2 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_nonneg
  have expand : (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ^ 2
      = (Real.sqrt (n : ℝ)) ^ 2 + (Real.sqrt (m : ℝ)) ^ 2
        + 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by ring
  rw [expand, h1, h2]
have h_lt : Real.sqrt ((n : ℝ) + (m : ℝ)) < Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) := by
  rw [Real.sqrt_lt' hsum_pos, h_exp]
  linarith
```
This drops the need for the original's separate `h_sq_lt` have-block entirely — the whole
inequality now reduces to `linarith` over ordinary real arithmetic once `h_exp` and `h_cross`
(the `2√n√m > 0` cross term) are in scope.

### 2.9 Everything not listed above compiled unchanged

`LocalizedReflexive`, `reflexive_minimality`, `reflexive_isomorphism`, the forward direction of
`prime_incompressibility`, `diagonal_eq_sqrt_two`, `diagonal_is_irrational`,
`no_common_rational_measure`, `period_incommensurability`, `TriadicState`, `geometric_mean_bridge`,
and `equipartition_fixed_point` needed no changes beyond what's listed in §2.1–§2.3.

---

## 3. Result

`PrimitiveReflexivity/Foundations.lean` builds with 0 errors and 0 `sorry`. Confirmed
independently via `#print axioms` on all 12 theorems — every one depends only on Lean/Mathlib's
standard trust base (`propext`, `Classical.choice`, `Quot.sound`), never on `sorryAx`. Full detail
in `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` in this same folder.

---

## 4. Addendum — Group Inequivalence (ℝ, +) ≇ U(1)

Closes the gap left by Theorem 3 Part 1 not being in the original 12-theorem suite (Part 2,
`period_incommensurability`, was already covered above). Drafted separately in
`Group_Inequivalence_Implementation_Brief.md` and added to
`PrimitiveReflexivity/Foundations.lean` at the end of Section VII.

### 4.1 As supplied (brief §1)

```lean
import Mathlib.Analysis.Complex.Circle

theorem group_inequivalence
    (f : ℝ ≃ Circle) (hf : ∀ x y : ℝ, f (x + y) = f x * f y) : False := by
  have hf0 : f 0 = 1 := by
    have h : f 0 = f 0 * f 0 := by simpa using hf 0 0
    have heq : f 0 * 1 = f 0 * f 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel heq).symm
  obtain ⟨r, hr⟩ := f.surjective (-1 : Circle)
  have hneg1 : (-1 : Circle) * (-1 : Circle) = 1 := by
    rw [neg_mul_neg, one_mul]
  have h1 : f (r + r) = 1 := by rw [hf, hr, hneg1]
  have h2 : r + r = 0 := f.injective (h1.trans hf0.symm)
  have hr0 : r = 0 := by linarith
  rw [hr0, hf0] at hr
  exact Circle.neg_ne_self 1 hr.symm

theorem real_not_equiv_circle : ¬ Nonempty (Multiplicative ℝ ≃* Circle) := by
  rintro ⟨g⟩
  apply group_inequivalence (Equiv.trans Multiplicative.ofAdd g.toEquiv)
  intro x y
  simp only [Equiv.trans_apply, MulEquiv.coe_toEquiv]
  have hadd : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  rw [hadd, map_mul]
```

### 4.2 What actually broke, and the fix

`group_inequivalence` (the unbundled form) compiled unchanged on the first attempt — none of the
brief's flagged risks (`Circle.neg_ne_self`, `Circle.instCommGroup`/`instHasDistribNeg`) materialized.

`real_not_equiv_circle` did not build. The brief's own top-flagged risk was the `hadd := rfl` line;
that line was in fact fine. The real failure was the following step, `rw [hadd, map_mul]`:

```
error: PrimitiveReflexivity/Foundations.lean:181:12: failed to synthesize instance of type class
  MulHomClass (Multiplicative ℝ ≃ Circle) (Multiplicative ℝ) Circle
error: PrimitiveReflexivity/Foundations.lean:175:75: unsolved goals
g : Multiplicative ℝ ≃* Circle
x y : ℝ
hadd : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y
⊢ MulHomClass (Multiplicative ℝ ≃ Circle) (Multiplicative ℝ) Circle
```

**Cause:** `Equiv.trans Multiplicative.ofAdd g.toEquiv` is a bare `Equiv` — composing through
`.toEquiv` strips off `g`'s `MulEquiv` bundling, so nothing in scope carries a `MulHomClass`
instance for `map_mul` to find, even though `g` itself has one.

**Fix:** replaced the `simp [...]` + `rw [hadd, map_mul]` pair with a `change` to the definitionally
equal goal stated directly in terms of `g` (not the composed `Equiv`), then closed it with `map_mul`
applied to `g` itself, which does carry the instance:

```lean
theorem real_not_equiv_circle : ¬ Nonempty (Multiplicative ℝ ≃* Circle) := by
  rintro ⟨g⟩
  apply group_inequivalence (Equiv.trans Multiplicative.ofAdd g.toEquiv)
  intro x y
  change g (Multiplicative.ofAdd (x + y)) = g (Multiplicative.ofAdd x) * g (Multiplicative.ofAdd y)
  have hadd : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  rw [hadd, map_mul]
```

(First tried `show` instead of `change` for that step; Lean's style linter flagged it —
`` `show` should only be used to indicate intermediate goal states for readability... this tactic
invocation changed the goal `` — because the stated goal isn't syntactically the one on screen, only
definitionally equal to it. `change` is the correct tactic for that and carries no such warning.)

### 4.3 Result

Builds with 0 errors, 0 `sorry`. `#print axioms` on both: `[propext, Classical.choice, Quot.sound]`
— the same standard trust base as the rest of the suite, no `sorryAx`. Theorem count for the project
is now 14; see `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` for the updated table.
