# Build Summary — PrimitiveReflexivity Lean 4 Formalization
**Date:** 2026-08-28
**Project dir:** `C:\Folders that need to be sorted\7 Projects\Compiler\PrimitiveReflexivity\` (new Lean 4 + Mathlib project — separate from the Moses/Porisis/DSIS trees, but same project owner and same record-keeping folder)
**Objective:** Stand up a Lean 4 + Mathlib project from scratch and formally verify (zero `sorry`) the first-order logic (reflexivity axioms), arithmetic descent / prime-identity theorem, dual-axis geometric incommensurability theorems, and triadic-state / mediator-defect theorems from Jonathon's paper "Foundations of Primitive Reflexivity: The Discrete Node-First Ontology, Axis Incommensurability, and the Phase-Drift Definition of Angles."
**Outcome:** Full success. `lake build` completes with 0 errors on all 12 theorems/lemmas. Independently confirmed via `#print axioms` on every theorem that the only axioms in play are Lean's standard trust base (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx` anywhere, which is a stronger check than grepping the source for the literal word "sorry."

---

## 1. What Was Built

- **Toolchain from nothing:** neither `elan`, `lake`, nor `lean` existed on the machine. Installed via `winget install Lean.Elan` (found as package `Lean.Elan` v4.2.4), which registers the `elan`/`lake`/`lean`/`leanc` command aliases. Set a default toolchain (`elan default leanprover/lean4:stable`) so `lake` itself could bootstrap before the project's own pinned toolchain existed.
- **Project scaffold:** `lake new PrimitiveReflexivity math`, which pulled Lean 4.33.1 (pinned by Mathlib) and cloned Mathlib at rev `0df444a360eaa60ab8c11dca51a86af692955474`, plus its transitive deps (batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli). The `math` template's post-update hook builds the `cache` tool and auto-downloads the prebuilt Mathlib `.olean` cache (8,690 files) from Azure blob storage, so nothing had to be compiled from Mathlib source.
- **`PrimitiveReflexivity/Foundations.lean`** — the formalization itself, four sections matching the paper:
  - **Reflexivity axioms:** `LocalizedReflexive` typeclass, `reflexive_minimality`, `reflexive_isomorphism`.
  - **Arithmetic descent / prime identity:** `DivSet`, `ArithmeticPerSeIdentity`, `prime_incompressibility` (iff between `Nat.Prime` and the divisor-set characterization).
  - **Dual-axis incommensurability:** `manhattan_step`/`diagonal_step`/`delta_gap`, `manhattan_is_rational`, `diagonal_is_irrational`, `no_common_rational_measure`, `delta_gap_pos`, `two_pi_irrational`, `period_incommensurability`.
  - **Triadic state / mediator defect:** `TriadicState` structure, `geometric_mean_bridge`, `mediator_defect`, `mediator_defect_positive`, `equipartition_fixed_point`.
- **`PrimitiveReflexivity/AxiomCheck.lean`** — a verification-only file (`#print axioms` on all 12 theorems) built once to independently confirm the trust base, then unlinked from the default build target so the shipped deliverable is exactly `Foundations.lean` as requested. The file is still in the project directory and can be rebuilt on demand with `lake build PrimitiveReflexivity.AxiomCheck`.

---

## 2. Problems Encountered and How They Were Fixed

### 2.1 Self-inflicted: ran `lake update` concurrently with `lake new`'s still-running cache download
`lake new`'s post-update hook was still decompressing the 8,690-file Mathlib cache when a `lake update` was started in the same project directory. Both processes hit the same global cache at `C:\Users\Divin\.cache\mathlib\` simultaneously; Windows file locking produced ~30 `Access is denied (os error 5)` errors on `.ltar` cache files, and **both** commands ultimately exited 1 — including the original `lake new`, which had appeared to finish (a `ps` check briefly showed no matching process, coincidentally because of PID reuse on Windows, not because the job was actually done).
**Fix:** confirmed no `lake`/`lean` processes were running, then re-ran `lake update` alone, sequentially. It completed cleanly against the now-consistent cache.

### 2.2 The pasted code targeted an older Mathlib API — real build errors, not infrastructure noise
Once the file actually compiled, it surfaced genuine problems in the supplied code against the pinned Mathlib rev (`0df444a3`). These were fixed one at a time, verifying each fix against the actual Mathlib source before applying it (not guessed):

- **Three imports had moved:**
  - `Mathlib.Data.Real.Irrational` → split into `Mathlib.NumberTheory.Real.Irrational` (the `Irrational` def and `irrational_sqrt_two`) and `Mathlib.Analysis.Real.Pi.Irrational` (pi-irrationality, previously reachable transitively, now needs its own import).
  - `Mathlib.Data.Complex.Exponential` → `Mathlib.Analysis.Complex.Exponential`.
  - `Mathlib.Topology.Instances.Real` (used to be a single file) → is now a directory; the umbrella import is `Mathlib.Topology.Instances.Real.Lemmas`.
- **Two identifiers renamed:** `Real.irrational_pi` → `irrational_pi` (declared at top level, not inside `namespace Real`, in `Mathlib.Analysis.Real.Pi.Irrational`). `Irrational.rat_mul` → `Irrational.ratCast_mul` (confirmed exact signature — `(h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x)` — by reading `Mathlib/NumberTheory/Real/Irrational.lean` directly).
- **Three `def`s needed `noncomputable`:** `diagonal_step`, `delta_gap`, `mediator_defect` all bottom out in `Real.sqrt`, which is itself noncomputable (built on `Classical.choice`). The original code didn't mark them, so Lean's code generator rejected them even though every proof about them still type-checked.
- **`manhattan_is_rational`'s closing `rfl` was wrong, not just outdated:** after `push_cast`, the goal is `(2:ℝ) = 1 + 1` — numeral `2` is not *definitionally* `1+1` for a general semiring instance (it goes through `OfNat`), so `rfl` was never going to close this on any Mathlib version. Replaced with `norm_num`.
- **`delta_gap_pos`'s `Real.sqrt 4 = 2` step was also genuinely broken:** `norm_num` alone can't evaluate `Real.sqrt` of a literal. Replaced the whole `Real.sqrt 2 < 2` sub-proof with one call to `Real.sqrt_lt'` (`0 < y → (√x < y ↔ x < y^2)`), reducing it to `2 < 2^2`, which `norm_num` closes trivially.
- **`mediator_defect_positive` had a fragile, actually-broken step:** it tried `apply (Real.sqrt_lt_sqrt_iff _).mp` against a goal of the form `√(n+m) < √n + √m` — but `Real.sqrt_lt_sqrt_iff` requires *both* sides to be `Real.sqrt` of something, and `√n + √m` is a sum, not a single sqrt application. `apply`'s unifier didn't fail outright; it silently deferred a metavariable, producing nonsense downstream goals (`⊢ √(n+m) < 0`) that no amount of `linarith` could close. This was caught by reading the actual error context (an unexplained `a✝ : √(↑n + ↑m) < 0` hypothesis is not something a correct proof produces), not just by seeing red text. Rewrote the step from scratch using `Real.sqrt_lt'` directly against an explicit algebraic expansion `(√n+√m)² = n+m+2√n√m`, which reduces the whole inequality to `linarith` over ordinary real arithmetic.
- **`prime_incompressibility`'s final contradiction steps used a projection that doesn't exist:** `hm_gt1.trans_le (le_refl 1)` assumed a `Nat.le.trans_le` field that Lean's environment doesn't contain. Both closing bullets are pure arithmetic contradictions once `m` is substituted (`2 ≤ 1` and `p < p`), so replaced both with `omega`.

None of these were style preferences — every one was a genuine compile error, confirmed by reading the actual Mathlib source (`grep`, not memory) before writing the replacement.

---

## 3. What Was Tested, and What the Results Mean

### 3.1 `lake build` on the default target
Final build: **0 errors, 2 warnings** (a deprecated-lemma-name notice for `Set.mem_setOf_eq`, and a linter suggestion to merge two `intro` calls — both cosmetic, neither affects correctness). `Build completed successfully (2742 jobs)`.

### 3.2 Independent axiom audit (`#print axioms`) on all 12 theorems/lemmas
| Theorem | Axioms |
|---|---|
| `reflexive_minimality` | *(none)* |
| `reflexive_isomorphism` | `Quot.sound` |
| `prime_incompressibility` | `propext`, `Quot.sound` |
| `manhattan_is_rational` | `propext`, `Classical.choice`, `Quot.sound` |
| `diagonal_is_irrational` | `propext`, `Classical.choice`, `Quot.sound` |
| `no_common_rational_measure` | `propext`, `Classical.choice`, `Quot.sound` |
| `delta_gap_pos` | `propext`, `Classical.choice`, `Quot.sound` |
| `two_pi_irrational` | `propext`, `Classical.choice`, `Quot.sound` |
| `period_incommensurability` | `propext`, `Classical.choice`, `Quot.sound` |
| `geometric_mean_bridge` | `propext`, `Classical.choice`, `Quot.sound` |
| `mediator_defect_positive` | `propext`, `Classical.choice`, `Quot.sound` |
| `equipartition_fixed_point` | `propext`, `Classical.choice`, `Quot.sound` |

All three axioms that appear are Lean/Mathlib's standard trust base — the same three nearly every nontrivial Mathlib theorem depends on (real numbers are built as a quotient of Cauchy sequences, which needs `Quot.sound`; classical real-number reasoning needs `Classical.choice`; `propext` is baseline for propositional extensionality). **`sorryAx` appears nowhere.** This is a stronger guarantee than grepping the source for the literal word "sorry," since it would also catch a `sorry` introduced through a macro or tactic that doesn't literally spell the word.

**Implication:** every theorem in `Foundations.lean` — the reflexivity axioms, the prime-incompressibility iff, both incommensurability directions (Manhattan-rational / diagonal-irrational), the `2π` non-commensurability result, the mediator-defect positivity theorem, and the 45°-equipartition fixed point — is a genuine, machine-checked proof from Lean/Mathlib's kernel, not an assumed or stubbed result.

---

## 4. Final State

Files in `C:\Folders that need to be sorted\7 Projects\Compiler\PrimitiveReflexivity\`:
- `PrimitiveReflexivity/Foundations.lean` — the deliverable, 0 `sorry`, builds clean.
- `PrimitiveReflexivity/AxiomCheck.lean` — verification-only, not part of the default `lake build` (unlinked from `PrimitiveReflexivity.lean`'s import list after use); rerun manually with `lake build PrimitiveReflexivity.AxiomCheck` if the file is ever touched again.
- `PrimitiveReflexivity/Basic.lean` — untouched scaffold file from `lake new`.
- `PrimitiveReflexivity.lean` — root module, imports `Basic` and `Foundations`.
- `lean-toolchain` — pins `leanprover/lean4:v4.33.1`.
- `lakefile.toml` — pins `mathlib` to `rev = "v4.33.1"` under `leanprover-community` scope.
- `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` — copy of this build summary.
- `Theorems_Original_and_Adjustments.md` — the theorem code as originally supplied, with every adjustment documented against it (see that file for the line-by-line diff and rationale).

Not yet done / open items: none blocking. If future paper sections are formalized in this project, follow the same discipline used here — read the actual Mathlib source for a lemma's current name/signature before using it, rather than trusting a remembered API, since Mathlib's file layout and lemma names do shift between revisions.
