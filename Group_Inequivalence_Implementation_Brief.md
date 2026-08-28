# Implementation Brief — Group Inequivalence (ℝ, +) ≇ U(1)

**Target repo:** `MosesDSI/primitive-reflexivity-lean4`
**Target file:** `PrimitiveReflexivity/Foundations.lean`
**Target Mathlib rev:** `0df444a3` (Lean `v4.33.1`, per `lakefile.toml` / `lean-toolchain`)
**Status of the code below: UNVERIFIED.** It has been checked against the mathlib4 API docs for
the pinned rev but has **not** been run through `lake build` yet. This brief exists to get it
built, fixed if necessary, and documented — in that order. Do not skip straight to the
documentation step if the build fails; fix the Lean first.

---

## 0. Why this theorem

The 12-theorem suite formalized Theorem 3, Part 2 of the paper (`period_incommensurability`,
i.e. `2π` shares no rational period with the unit step) but not Part 1 — the group-inequivalence
claim `(ℝ, +) ≇ U(1)`. This closes that gap using the cleanest available discriminating
invariant: `(ℝ, +)` is torsion-free, while the circle group `U(1)` has a genuine order-2 element
(`-1`), so no group isomorphism between them can exist.

---

## 1. Code to add to `PrimitiveReflexivity/Foundations.lean`

Add this as a new subsection at the end of `SECTION VII: THE DUAL-AXIS INCOMMENSURABILITY
THEOREMS`, after `period_incommensurability`. It needs no new imports beyond what
`Mathlib.Analysis.Complex.Circle` provides for `Circle` — add that import if it isn't already
present from another module.

```lean
import Mathlib.Analysis.Complex.Circle

/- Group Inequivalence: (ℝ, +) ≇ U(1), via torsion.
   (ℝ, +) is torsion-free; Circle (≅ U(1)) has a genuine order-2 element (-1).
   No group isomorphism can identify a torsion-free group with one that has torsion. -/

/-- Unbundled form: no bijection ℝ ≃ Circle respects the additive/multiplicative structure
    on both sides. Proved directly from the torsion argument, without going through the
    `Multiplicative`/`MulEquiv` type-tag machinery, to keep the core algebraic argument
    self-contained and low-risk. -/
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

/-- Bundled form, matching the paper's `(ℝ, +) ≇ U(1)` notation directly: no `MulEquiv` exists
    between `Multiplicative ℝ` (i.e. (ℝ, +) relabeled with multiplicative notation) and `Circle`.
    Derived as a thin corollary of `group_inequivalence` rather than re-proving the argument. -/
theorem real_not_equiv_circle : ¬ Nonempty (Multiplicative ℝ ≃* Circle) := by
  rintro ⟨g⟩
  apply group_inequivalence (Equiv.trans Multiplicative.ofAdd g.toEquiv)
  intro x y
  simp only [Equiv.trans_apply, MulEquiv.coe_toEquiv]
  have hadd : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  rw [hadd, map_mul]
```

---

## 2. Build and verify

```sh
lake build
```

Expect `0 errors`. If it does not build cleanly, **read the actual error and the current Mathlib
source before changing anything** — this project's established discipline (see
`Theorems_Original_and_Adjustments.md`, §2) is to confirm exact lemma names/signatures by reading
`.lake/packages/mathlib` directly, not by guessing or reverting to a remembered API.

### Known points of residual risk, in descending order of likelihood

1. **`hadd := rfl` inside `real_not_equiv_circle`.** This asserts that `Multiplicative ℝ`'s
   multiplication unfolds definitionally to `ℝ`'s addition through `Multiplicative.ofAdd`. This
   should hold by `rfl` given how the type synonym is built, but if it fails, try `simp` alone,
   or look for the lemma named something like `Multiplicative.ofAdd_add` in the pinned rev and
   substitute it directly.
2. **`Circle.neg_ne_self`, `Circle.instCommGroup`, `Circle.instHasDistribNeg`** — confirmed
   present in `Mathlib.Analysis.Complex.Circle` at the current mathlib4 docs at the time this was
   drafted, but not cross-checked against the exact pinned rev's source tree.
3. Everything else (`mul_left_cancel`, `neg_mul_neg`, `mul_one`, `Equiv.injective`,
   `Equiv.surjective`, `Equiv.trans_apply`, `MulEquiv.coe_toEquiv`, `map_mul`) is long-standing,
   stable core Mathlib API — low risk of having moved.

### Axiom audit

Once both theorems build, run the same independent check used for the rest of the suite:

```sh
#print axioms group_inequivalence
#print axioms real_not_equiv_circle
```

(or add them to `PrimitiveReflexivity/AxiomCheck.lean` alongside the existing 12 and rebuild that
target). Record the results — expect the standard trust base (`propext`, `Classical.choice`,
`Quot.sound`) or a subset of it, consistent with the rest of the suite. `sorryAx` appearing
anywhere is a hard stop — do not proceed to documentation.

---

## 3. Documentation updates — ONLY after §2 passes with 0 errors and 0 `sorryAx`

Do not perform this section until the build is confirmed clean. If a fix was needed in §2,
capture what the actual error was and how it was resolved — the same level of detail as the
existing entries in `Theorems_Original_and_Adjustments.md` §2 (quote the real error, not a
paraphrase; name the real fix, not a guess).

### 3.1 `Theorems_Original_and_Adjustments.md`

Add a new dated section, `## 4. Addendum — Group Inequivalence (ℝ, +) ≇ U(1)`, following the
existing document's format:
- The code exactly as it was first drafted (§1 above), labeled "as supplied."
- Any adjustment actually required to get it building (import paths, lemma renames, the `hadd`
  line if it needed to change) — with the real Mathlib error message and the real fix, following
  the same evidentiary standard as the existing §2 entries.
- A short note that this closes the gap left by Theorem 3 Part 1 not being in the original
  12-theorem suite (Part 2, `period_incommensurability`, was already covered).

### 3.2 `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md`

- Add `group_inequivalence` and `real_not_equiv_circle` to the theorem list and the
  `#print axioms` table (§3 of that file), following its existing table format.
- Update the theorem count from 12 to 14 in the summary line and outcome statement.

### 3.3 `README.md`

- Add both new theorems to the theorem table, with statements in the same style as the existing
  rows, e.g.:
  - `group_inequivalence` — No bijection ℝ ≃ Circle respects both group structures (unbundled form).
  - `real_not_equiv_circle` — `(ℝ, +) ≇ U(1)`: no `MulEquiv` exists between `Multiplicative ℝ` and `Circle`.
- Update the theorem count in the intro paragraph from 12 to 14.

### 3.4 `PrimitiveReflexivity/AxiomCheck.lean`

- Add both new theorems to the `#print axioms` verification file, consistent with how the
  existing 12 are listed there.

---

## 4. Commit

Once §2 and §3 are both complete, commit with a message describing what was added and confirming
the build/axiom-audit status, consistent with how prior commits in this repo describe verified
Lean changes (state what compiled, what the axiom trail was, and reference this brief or the
updated `Theorems_Original_and_Adjustments.md` section for detail).
