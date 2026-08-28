# Acknowledgments & Human–Machine Formalization Note

## Authorship

The conceptual foundations, axiomatic framework, and physical/geometric ontology formalized in
this repository — the reflexivity axioms, the arithmetic-descent / prime-identity theorem, the
dual-axis incommensurability theorems, and the triadic-state / mediator-defect theorems — were
authored by **Jonathon Pearson**, from the paper *"Foundations of Primitive Reflexivity: The
Discrete Node-First Ontology, Axis Incommensurability, and the Phase-Drift Definition of Angles."*
The mathematical claims formalized here are his; nothing in this repository originates the theory
itself.

## The formalization pipeline

This repository is the result of a two-stage human–AI pipeline, and both stages are worth naming
explicitly rather than folding into a single undifferentiated "AI-assisted" credit:

- **Initial formal specification — Google Gemini.** The first translation of the paper's theorem
  statements into Lean 4 syntax — the shape of the definitions and proof attempts this repository
  builds on — was produced by Gemini.
- **Environment setup, Mathlib alignment, and proof engineering — Claude Code (Anthropic).**
  I am **Claude**, specifically the **Claude Sonnet 5** model, running as **Claude Code**
  (Anthropic's CLI agent), operated by Jonathon on 2026-08-28. My contribution to this repository,
  concretely:
  - Installed the Lean toolchain (`elan`/`lake`/`lean`) from nothing and scaffolded the project
    (`lake new PrimitiveReflexivity math`), pinning Lean `v4.33.1` and Mathlib rev `0df444a3`.
  - Took Gemini's initial Lean translation and made it actually build. This was not a rename pass —
    it required reading the real Mathlib source in `.lake/packages/mathlib` to confirm the correct
    fix in each case, rather than guessing from a remembered API:
    - Relocated three imports that had moved in current Mathlib (`Mathlib.Data.Real.Irrational` →
      split across `Mathlib.NumberTheory.Real.Irrational` + `Mathlib.Analysis.Real.Pi.Irrational`;
      `Mathlib.Data.Complex.Exponential` → `Mathlib.Analysis.Complex.Exponential`;
      `Mathlib.Topology.Instances.Real` → `Mathlib.Topology.Instances.Real.Lemmas`).
    - Fixed two renamed identifiers (`Real.irrational_pi` → `irrational_pi`; `Irrational.rat_mul` →
      `Irrational.ratCast_mul`).
    - Added missing `noncomputable` annotations on three `Real.sqrt`-based definitions.
    - Corrected a `rfl` that could never close (`(2:ℝ) = 1+1` is not definitional) and a
      `norm_num` call asked to evaluate `Real.sqrt 4` directly, which it can't do unassisted.
    - Diagnosed and rewrote a genuinely broken proof step in `mediator_defect_positive`, where
      `Real.sqrt_lt_sqrt_iff` was applied against a goal shape it doesn't match
      (`√(n+m) < √n + √m` — the right side isn't a single `sqrt` application), which was silently
      producing nonsense subgoals rather than failing loudly.
    - Replaced a nonexistent `Nat.le.trans_le` projection with `omega`.
  - Independently audited the result via `#print axioms` on all 12 theorems — confirming every one
    depends only on Lean's standard trust base (`propext`, `Classical.choice`, `Quot.sound`), never
    on `sorryAx`, as a stronger check than grepping the source for the literal word "sorry."
  - Set up the public repository, GitHub Actions CI (`leanprover/lean-action`), and confirmed the
    build passes independently on a clean GitHub-hosted runner, not just on Jonathon's machine.

## Verification kernel

Lean `4.33.1` / Mathlib rev `0df444a3`. **0 `sorry`**, 12/12 theorems axiom-audited clean.

## What "verified" means here — and what it doesn't

Lean's kernel guarantees that every theorem in `Foundations.lean` follows from Mathlib's axioms,
*given the Lean definitions as written*. That is a real, machine-checked guarantee, and it's the
reason this is publishable for others to independently re-run rather than just taken on faith.

It does **not**, by itself, guarantee that the Lean encoding is a faithful translation of what the
paper means — that a given Lean `def` captures the intended physical/geometric concept, or that a
theorem's Lean statement says what its name claims it says in the paper's terms. That translation
step (paper concept → Lean statement) is a judgment call made once by Gemini and reviewed, not
independently re-derived, by Claude. Readers checking this repository should distinguish "the Lean
code type-checks" (verified, strongly) from "the Lean code says what the paper says" (a translation
claim, worth reading the statements yourself to confirm).
