# Build Summary — Group Inequivalence Theorem Addition + CI Workflow Repair
**Date:** 2026-08-28
**Project dir:** `C:\Folders that need to be sorted\7 Projects\Compiler\PrimitiveReflexivity\` (repo `MosesDSI/primitive-reflexivity-lean4`)
**Follows:** `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` (the original 12-theorem formalization).
**Objective:** Execute `Group_Inequivalence_Implementation_Brief.md` — add, build-verify, axiom-audit, and document the `(ℝ, +) ≇ U(1)` theorem pair the original 12-theorem pass had left out — then, separately, diagnose and repair the two failing GitHub Actions workflows discovered on the repo's very first push, and clean up three GitHub-Copilot-authored PRs that had been opened autonomously against those failures.
**Outcome:** Full success on both fronts. 14/14 theorems build clean (0 errors, 0 `sorry`), independently axiom-audited. Both CI failures resolved — one had already self-resolved, the other fixed via a merged PR. Repo now has 0 open PRs and no known outstanding CI issues.

---

## 1. What Was Built

- Added `group_inequivalence` (unbundled torsion argument: no bijection `ℝ ≃ Circle` respects both group structures) and `real_not_equiv_circle` (bundled corollary: no `MulEquiv` between `Multiplicative ℝ` and `Circle`) to `PrimitiveReflexivity/Foundations.lean`, per the brief. Closes Theorem 3 Part 1 of the paper (Part 2, `period_incommensurability`, was already in the original suite).
- Updated `PrimitiveReflexivity/AxiomCheck.lean`, `Theorems_Original_and_Adjustments.md` (new §4 addendum), `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` (theorem count, axiom table, §2.3), and `README.md` (theorem table, counts) to reflect the 14-theorem state.
- Committed (`7a88eb0`) and pushed to `origin/master`.
- Diagnosed both failing GitHub Actions runs from the repo's initial commit (`Lean Action CI` and `Create Release`).
- Reviewed, merged, and closed three GitHub-Copilot-authored PRs (`#1`, `#2`, `#3`) that had been opened autonomously against those two failures, without having been asked for by this session.

---

## 2. Problems Encountered and How They Were Fixed

### 2.1 `real_not_equiv_circle` — `map_mul` instance failure through a stripped `Equiv`
Full detail already recorded in `Theorems_Original_and_Adjustments.md` §4; summarized here for this session's record. The brief's own top-flagged risk (the `hadd := rfl` line) was fine; the actual failure was one step later:
```
error: ...Foundations.lean:181:12: failed to synthesize instance of type class
  MulHomClass (Multiplicative ℝ ≃ Circle) (Multiplicative ℝ) Circle
```
**Cause:** composing `g : Multiplicative ℝ ≃* Circle` into a plain `Equiv` via `Equiv.trans Multiplicative.ofAdd g.toEquiv` strips the `MulEquiv` bundling before `map_mul` runs, so no `MulHomClass` instance is in scope. **Fix:** `change`d the goal to its definitionally-equal form stated directly in terms of `g`, then closed it with `map_mul` applied to `g` itself. (First tried `show` for that step; Lean's style linter flagged it as changing the goal, not just restating it — switched to `change`, which is warning-free.)

### 2.2 CI diagnosis — two independent failures on the repo's initial push
Investigated via `gh run list` / `gh run view --log` rather than assuming either failure was still live:
- **`Lean Action CI`**: `docgen-action`'s Pages-deploy step failed with `HttpError: Not Found` / `Failed to create deployment (status: 404) ... Ensure GitHub Pages has been enabled`. Confirmed via `gh api repos/.../pages` that Pages **is** enabled now, and that the very next push (`268f70a`, "Add acknowledgments") already ran this same workflow to a clean success including doc deploy. **Already self-resolved** before this session started — no code change needed, just verified rather than assumed.
- **`Create Release`** (`create-release.yml`, triggers only on push to main/master when `lean-toolchain` changes): the `leanprover-community/lean-release-tag@v1` action's `create-tags.sh` runs `git log <before>..<after>`. On a repo's first-ever push, GitHub sets `before` to the all-zero SHA (`0000...0000`), which is not a valid git revision:
  ```
  fatal: Invalid revision range 0000000000000000000000000000000000000000..b64823772aaae1d3dccd71bac137ea2031d3bca0
  ```
  This workflow hadn't re-triggered since (neither later commit touched `lean-toolchain`), so it was dormant, not currently blocking — but would fail again on the next Lean/Mathlib version bump if left unfixed.

### 2.3 Three autonomous Copilot PRs found already open, cleaned up per user direction
A GitHub Copilot cloud agent (`app/copilot-swe-agent`) had independently opened three PRs against the two failures above, unprompted by this session:
- **PR #1** (draft) — `deploy: false` on `docgen-action` to skip the Pages deploy. Root cause already gone (§2.2) — moot.
- **PR #2** (draft) and **PR #3** (open) — near-duplicate one-line fixes for the release-tag bug, both mapping the all-zero `before` sentinel to git's well-known empty-tree hash (`4b825dc642cb6eb9a060e54bf8d69288fbee4904`) so the revision range is always valid.
- Verified PR #3's own CI (two `Lean Action CI` runs) was green, merged it (`gh pr merge 3 --merge --delete-branch`) — now `2e2e4cc` on `master`.
- Closed #2 as a duplicate of #3, and #1 as moot, each with an explanatory comment; both branches deleted.
- Flagged to the user, rather than silently cleaning up, that this Copilot activity was unprompted — worth them checking whether an autofix/coding-agent integration is enabled on the repo/org that they didn't intend.
- User's direction: **merge #3, close #1 and #2** — executed exactly that, no more, no less.

---

## 3. What Was Tested, and What the Results Mean

- **`lake build`** (full default target): 0 errors, 14/14 theorems, `Build completed successfully (2745 jobs)`. Only the two pre-existing cosmetic warnings remain (deprecated `Set.mem_setOf_eq`, a merge-`intro` linter suggestion) — unrelated to this session's changes.
- **`#print axioms`** on `group_inequivalence` and `real_not_equiv_circle` (via `AxiomCheck.lean`): both `[propext, Classical.choice, Quot.sound]` — the same standard trust base as the original 12, no `sorryAx`.
- **PR #3's CI**: both `Lean Action CI` runs (job `build`) completed `SUCCESS` before merge — confirmed via `statusCheckRollup`, not assumed from the PR description alone.
- **Post-merge sync**: `git fetch` + `git pull --ff-only` brought local `master` to `2e2e4cc` cleanly (fast-forward, no conflicts) — confirms the merge didn't diverge from what was pushed.

---

## 4. Final State

- Local and remote `master` both at `2e2e4cc`.
- Repo has **0 open PRs**.
- Files changed this session: `PrimitiveReflexivity/Foundations.lean`, `PrimitiveReflexivity/AxiomCheck.lean`, `Theorems_Original_and_Adjustments.md`, `README.md`, `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md`, `Group_Inequivalence_Implementation_Brief.md` (newly tracked), `.github/workflows/create-release.yml` (via merged PR #3).
- Not yet done / open items: none blocking. The `Create Release` fix is merged but has not yet been exercised against a real `lean-toolchain` change (it's only proven correct by inspection + the PR author's own reasoning, not by a live all-zero-SHA push in this repo) — worth a quiet confirmation the next time the Lean/Mathlib pin is bumped.
