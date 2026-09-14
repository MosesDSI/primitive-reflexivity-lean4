# Build Summary — Discrete Square Unfolding Formalization

**Date:** 2026-09-14
**Project dir:** `PrimitiveReflexivity\` (repo `MosesDSI/primitive-reflexivity-lean4`), new subfolder `Geometry\`
**File:** `PrimitiveReflexivity/Geometry/SquareUnfolding.lean`
**Objective:** Review and verify a user-supplied draft formalizing the boundary metric of a square `[0,s]×[0,s]`, its canonical unfolding into the interval `[0,4s]`, and isometric preservation of edge lengths — four theorems (`unfold_bounds`, `unfold_isometry_same_edge`, `unfold_corner_adjacency`, `perimeter_unfold_conservation`).
**Outcome:** Draft did not compile as supplied. Two real bugs found by compiling, not reading; both fixed. Module now builds clean and is wired into the repo's default target.

---

## 1. Bugs found

1. **Missing tactic imports.** The draft imported only `Mathlib.Data.Real.Basic` and `Mathlib.Algebra.Order.Ring.Defs`, neither of which transitively pulls in `linarith` or `ring` at this repo's pinned Mathlib rev (`v4.33.1`). Every proof using either tactic failed with "unknown tactic," which cascaded into a parse error on `refine ⟨by ring, by ring, by ring⟩` (Lean tried to read it as a 1-field `And.intro`). Fixed by adding `import Mathlib.Tactic.Linarith` and `import Mathlib.Tactic.Ring`.

2. **Unreduced `Fin.val` casts.** `SquareEdge.index : SquareEdge → Fin 4` meant `edgeOffset` carried a `((e.index).val : ℝ)` cast. `dsimp [SquareEdge.index]` unfolds the match but does not reduce `Fin.val` of the resulting numeral literal — `linarith`/`ring` then treated `↑0 * s`, `↑1 * s`, `↑↑3 * s` as opaque atoms rather than `0`, `s`, `3*s`. The `bottom`/`right`/`top` cases happened to clear once the tactic imports were added, but the `left` case (`Fin.val (3 : Fin 4)`) never reduced under `dsimp`, `simp`, or `simp only` — `unfold_bounds`'s `.left` case and the `ring` calls touching `.left` in `unfold_corner_adjacency`/`perimeter_unfold_conservation` kept failing with the literal `3` surviving as `↑↑3` in the goal state.

   Since nothing in the file uses `Fin 4`'s bounded/modular structure — the index is only ever cast straight to `ℝ` — `SquareEdge.index` was changed to return plain `ℕ`. Same four values (`0,1,2,3`), but now a trivial `Nat.cast` of a literal, which `ring`/`linarith` normalize natively without any extra reduction step. This is both the fix and a simplification (removes an unused typeclass dependency).

## 2. Verification

- `lake build PrimitiveReflexivity.Geometry.SquareUnfolding`: 853/853 jobs, 0 errors, 0 warnings.
- `#print axioms` on all four theorems (`unfold_bounds`, `unfold_isometry_same_edge`, `unfold_corner_adjacency`, `perimeter_unfold_conservation`): `[propext, Classical.choice, Quot.sound]` — Lean's standard trust base only (expected for anything touching `ℝ`, built via Cauchy-sequence quotients). **Zero `sorryAx`.**
- Wired `import PrimitiveReflexivity.Geometry.SquareUnfolding` into the root `PrimitiveReflexivity.lean`, matching how `Theta0Photon.lean` wires in `ContinuumBridge.lean` (2026-09-11 precedent).
- Full project rebuild after wiring: `lake build` — **2746/2746 jobs, clean.** The two pre-existing warnings in `Foundations.lean` (a deprecated `Set.mem_setOf_eq`, an `intro`-suggestion note) are unrelated to this module and unchanged.

## 3. Git

Committed to `PrimitiveReflexivity` (`origin` = `github.com/MosesDSI/primitive-reflexivity-lean4`) and pushed, per the repo's standing Category B (engineering-report) documentation rule — no dispute content, a real technical retrospective on bugs caught by compilation. Staged exactly: `PrimitiveReflexivity/Geometry/SquareUnfolding.lean`, `PrimitiveReflexivity.lean` (import wiring), this file, and the companion `A_Comment_from_Claude/` entry + its README index update. Pre-existing unrelated untracked files in the working tree were left alone.
