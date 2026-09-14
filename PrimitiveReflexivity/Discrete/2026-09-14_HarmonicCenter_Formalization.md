# Build Summary — Discrete Harmonic Centers and Symmetric Partitions

**Date:** 2026-09-14
**Project dir:** `PrimitiveReflexivity\` (repo `MosesDSI/primitive-reflexivity-lean4`), new subfolder `Discrete\`
**File:** `PrimitiveReflexivity/Discrete/HarmonicCenter.lean`
**Objective:** Formalize the discrete interval `omega k = {1, ..., 2k+1}`, its harmonic center `k+1`, distance symmetry about that center, and (at `k = 10`) a mod-3 partition of `{1, ..., 21}` whose middle residue class contains the center and has the minimal total distance sum among the three classes.
**Outcome:** All four declarations (`harmonic_distance_symmetry`, `C1`/`C2`/`C3`, `harmonic_center_in_C2`, `tri_partition_distance_sums`) build clean. One tactic substitution from the original spec, documented below; everything else matches as specified.

---

## 1. Content

- `omega (k : ℕ) : Finset ℤ := Finset.Icc 1 (2 * (k : ℤ) + 1)` — the discrete interval.
- `harmonic_distance_symmetry (k : ℕ) (j : ℤ)`: `|(k+1-j) - (k+1)| = |(k+1+j) - (k+1)|`, proved by reducing both sides to `-j`/`j` via `ring` and closing with `abs_neg`.
- `C1`, `C2`, `C3`: the three residue classes of `Finset.Icc 1 21` mod 3 (`n % 3 = 1`, `= 2`, `= 0` respectively).
- `harmonic_center_in_C2 : (11 : ℤ) ∈ C2`, proved by `decide` (`11 % 3 = 2`).
- `distSum (p : ℤ) (s : Finset ℤ) : ℤ := ∑ c ∈ s, |c - p|`.
- `tri_partition_distance_sums : distSum 11 C1 = 37 ∧ distSum 11 C2 = 36 ∧ distSum 11 C3 = 37` — confirms the middle class containing the center has the strictly smallest total distance.

## 2. Deviation from spec: `decide`, not `norm_num`, for `tri_partition_distance_sums`

The spec asked for this theorem via `norm_num`. Tried it first as specified:
`norm_num [distSum, C1, C2, C3, Finset.sum_filter, Finset.Icc]` unfolded the
definitions but left the goal as an unevaluated
`∑ a ∈ LocallyFiniteOrder.finsetIcc 1 21, if a % 3 = 1 then |a - 11| else 0 = 37`
— `norm_num` has no extension that expands a `Finset.sum` over a concrete
`Finset.Icc`/`filter` into individual terms it can then sum numerically.
Switched to `decide`, the same tactic the spec already used for
`harmonic_center_in_C2` and the natural fit for a fully concrete, finite,
decidable computation over 21 elements. Ran clean in the same 15s as the rest
of the module — no measurable slowdown from the switch.

## 3. Verification

- `lake build PrimitiveReflexivity.Discrete.HarmonicCenter`: 930/930 jobs, 0 errors, 0 warnings.
- `#print axioms`:
  - `harmonic_distance_symmetry`: `[propext]` only (pure `ring`/`abs_neg`, no choice or quotient dependency).
  - `harmonic_center_in_C2`, `tri_partition_distance_sums`: `[propext, Classical.choice, Quot.sound]` — standard trust base only.
  - **Zero `sorryAx` across all three.**
- Wired `import PrimitiveReflexivity.Discrete.HarmonicCenter` into the root `PrimitiveReflexivity.lean`, following the same convention as `Geometry.SquareUnfolding` (2026-09-14, same day, prior session in this repo).
- Full project rebuild after wiring: `lake build` — **2747/2747 jobs, clean.** (One more than `SquareUnfolding`'s post-wiring count of 2746, since this module adds to that baseline.) The two pre-existing `Foundations.lean` warnings are unchanged and unrelated.

## 4. Git

Committed to `PrimitiveReflexivity` (`origin` = `github.com/MosesDSI/primitive-reflexivity-lean4`) and pushed, per the repo's standing Category B (engineering-report) documentation rule. Staged exactly: `PrimitiveReflexivity/Discrete/HarmonicCenter.lean`, `PrimitiveReflexivity.lean` (import wiring), this file, and the companion `A_Comment_from_Claude/` entry + README index update. Pre-existing unrelated untracked/deleted files in the working tree were left alone.
