# Build Summary — QS Additive Structure and Multiplicative Inverse (Roadmap Steps 1–2)

**Date:** 2026-09-24
**File:** `OrderObstruction.lean` (bare Lean 4, no Mathlib; not yet wired into the `lake` project — see §4)
**Objective:** Execute Section 9.3's roadmap Steps 1 ("Additive structure") and 2 ("Inverse") on the `QS` model of ℚ(√2), correct the `step`/`step_below`/`step_above` docstrings per Section 7.4's iterate-sequence correction, and independently verify the whole file (kernel + `leanchecker`).

---

## 1. Environment discrepancy found before starting

The task and `Order_Obstruction_Technical_Paper.pdf` both state Lean 4.34.1. This machine has no `4.34.1` toolchain installed — only `leanprover/lean4:v4.33.1` (elan) and `v4.34.0-rc2` (a pre-release). `PrimitiveReflexivity/lean-toolchain` and `lakefile.toml` (which pins `mathlib` to `v4.33.1`) both confirm the project's actual working toolchain is **v4.33.1**, not v4.34.1 — that version does not exist anywhere in this environment. All compilation and `leanchecker` replay below used v4.33.1, the toolchain the rest of this repo (`HarmonicCenter.lean`, `SquareUnfolding.lean`, etc.) already builds against. Flagging this now since the paper's stated reproduction environment is not reproducible as literally written.

## 2. Task 1 — docstring correction (Section 7.4)

Updated the docstrings on `step`, `step_below`, `step_above` in `QS` to state the corrected iterate structure: starting from 1, the sequence 1, 4/3, 7/5, 24/17, 41/29, … does not consist entirely of classical side-and-diagonal approximations. Only every other term (7/5, 41/29, …) is; the intermediate terms are the hyperbolic reflections of those terms across √2 under x ↦ 2/x (4/3 = 2/(3/2), 24/17 = 2/(17/12)). Comment-only change, no proof-relevant edits.

## 3. Task 2 — additive structure

Added `Add`, `Neg`, `Sub`, `Zero`, `One` instances on `QS`, all componentwise on the two `Rat` fields, plus `add_assoc`, `add_comm`, `zero_add`, `add_zero`, `add_left_neg`, `sub_eq_add_neg`. Every proof follows the file's existing pattern (`show` to unfold the instance to its literal `⟨_, _⟩` form, `congr 1 <;> grind`) — no new proof technique introduced.

## 4. Task 3 — conjugate, norm, inverse

- `conj (x : QS) : QS := ⟨x.a, -x.b⟩`, `norm (x : QS) : Rat := x.a*x.a - 2*(x.b*x.b)`.
- `norm_eq_zero_iff`: the `x.b ≠ 0` case reduces to `(x.a/x.b)*(x.a/x.b) = 2` (cleared via `Rat.div_mul_cancel`/`Rat.mul_div_cancel`, not a Mathlib field-division tactic — none is available here) and is discharged directly by `rat_no_sqrt_two`, exactly as the roadmap table specifies ("Proposition 1.1 guarantees a² − 2b² ≠ 0 for nonzero elements").
- `inv (x : QS) : QS := ⟨x.a / norm x, -x.b / norm x⟩`, `Inv QS` instance, `mul_inv_cancel`.
- `mul_inv_cancel`'s proof clears denominators by multiplying both components by `norm x` (nonzero, via `norm_eq_zero_iff`) and reduces to `Rat.mul_eq_zero`-based cancellation — the same discharge style `step_below`/`step_above` already use for `step`'s division, kept consistent rather than reaching for an untested general field-division tactic.

**Not done:** wiring `OrderObstruction.lean` into the `lake` project (moving it under `PrimitiveReflexivity/PrimitiveReflexivity/` and adding an import to the root `PrimitiveReflexivity.lean`). The task offered this as an option ("or a dedicated submodule … importing it") but Steps 1–2 as specified didn't require it, and the file already compiles and replays cleanly standalone via raw `lean`/`leanchecker`, matching the paper's own Appendix A method and its Section 10 "Standalone file" limitation. Flagging this as still open, not silently resolved.

## 5. Verification

- `lean OrderObstruction.lean` (v4.33.1): 0 errors. Every `#print axioms` line ran, including the eight new ones for `add_assoc`, `add_comm`, `zero_add`, `add_zero`, `add_left_neg`, `sub_eq_add_neg`, `norm_eq_zero_iff`, `mul_inv_cancel`, all `[propext, Classical.choice, Quot.sound]` — the same standard trust base as the rest of `QS`. Zero `sorryAx`.
- Escape-hatch scan (`sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`): no matches.
- Independent kernel replay: compiled to a fresh `.olean` and ran `leanchecker` against it (per the paper's Appendix A) — clean exit (0). A negative control (`leanchecker` pointed at a `LEAN_PATH` missing the compiled module) failed as expected ("Could not find any oleans for: OrderObstruction"), confirming the clean exit above is a genuine independent replay, not a silent no-op.
- Iterated once against errors before this: an initial draft of `norm_eq_zero_iff`'s `x.b = 0` case left an unsolved goal `{a:=0,b:=0} = 0` because `rw` doesn't auto-unfold the `Zero QS` instance for its closing `rfl` check — fixed by stating the target as the literal `⟨0, 0⟩` instead of `(0 : QS)` before the `rw`.

## 6. Git

Committed to `PrimitiveReflexivity` (`origin` = `github.com/MosesDSI/primitive-reflexivity-lean4`) and pushed, per the repo's standing Category B (engineering-report) rule — no dispute content, a real technical build. Staged exactly: `OrderObstruction.lean`, this file, and the companion `A_Comment_from_Claude/` entry + its README index update. The working tree has a number of pre-existing unrelated untracked/deleted files (from other sessions/tools) — left alone, not staged.
