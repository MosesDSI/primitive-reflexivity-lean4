# Primitive Reflexivity — Lean 4 Formalization

[![Lean Action CI](https://github.com/MosesDSI/primitive-reflexivity-lean4/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/MosesDSI/primitive-reflexivity-lean4/actions/workflows/lean_action_ci.yml)

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4) formalization of the
reflexivity axioms, arithmetic descent / prime-identity theorem, dual-axis geometric
incommensurability theorems, triadic-state / mediator-defect theorems, and the group-inequivalence
theorem `(ℝ, +) ≇ U(1)`, from the paper
**"Foundations of Primitive Reflexivity: The Discrete Node-First Ontology, Axis Incommensurability,
and the Phase-Drift Definition of Angles."**

All 14 theorems compile with **zero `sorry`**, verified against Lean `v4.33.1` /
Mathlib rev `0df444a3`. The badge above tracks the same build run on every push, on a clean
GitHub-hosted machine, independent of this author's environment — that's the point of publishing
it this way: anyone can re-run the exact same check.

## What's proved

All theorems live in [`PrimitiveReflexivity/Foundations.lean`](PrimitiveReflexivity/Foundations.lean).

| Theorem | Statement |
|---|---|
| `reflexive_minimality` | Any relation satisfying reflexivity pointwise is dominated by a locally-reflexive relation's own reflexivity. |
| `reflexive_isomorphism` | Local reflexivity transports across a type equivalence. |
| `prime_incompressibility` | `Nat.Prime p ↔` `p`'s divisor set is exactly `{1, p}` — primality as an "arithmetic per se identity." |
| `manhattan_is_rational` | The Manhattan (L¹) unit step `1 + 1` is rational. |
| `diagonal_is_irrational` | The Euclidean diagonal step `√(1² + 1²)` is irrational. |
| `no_common_rational_measure` | No rational number equals the diagonal step — restates the irrationality result as a non-existence claim. |
| `delta_gap_pos` | The gap between the Manhattan step and the diagonal step is strictly positive. |
| `two_pi_irrational` | `2π` is irrational. |
| `period_incommensurability` | No integers `m, n` (`n ≠ 0`) satisfy `m = n · 2π` — the unit period and the rotational period share no common rational measure. |
| `geometric_mean_bridge` | `√(n · n²) = n · √n` for natural `n`. |
| `mediator_defect_positive` | `√n + √m > √(n + m)` for positive naturals `n, m` — the "mediator defect" is always strictly positive. |
| `equipartition_fixed_point` | `cos²(π/4) = sin²(π/4) = 1/2`. |
| `group_inequivalence` | No bijection `ℝ ≃ Circle` respects both group structures (unbundled form). |
| `real_not_equiv_circle` | `(ℝ, +) ≇ U(1)`: no `MulEquiv` exists between `Multiplicative ℝ` and `Circle`. |

See [`Theorems_Original_and_Adjustments.md`](Theorems_Original_and_Adjustments.md) for the theorem
code exactly as originally drafted from the paper, and a line-by-line record of every adjustment
made to get it building against current Mathlib (moved imports, renamed lemmas, missing
`noncomputable` annotations, and two proof steps that were genuinely broken, not just
outdated — with the reasoning for each fix). See
[`2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md`](2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md)
for the full build log, including an independent `#print axioms` audit confirming every theorem
depends only on Lean's standard trust base (`propext`, `Classical.choice`, `Quot.sound`) and never
on `sorryAx`. You can re-run that audit yourself — it isn't part of the default build target, but
`PrimitiveReflexivity/AxiomCheck.lean` is in the repo:
```sh
lake build PrimitiveReflexivity.AxiomCheck
```

## Verifying it yourself

1. Install [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager) if you don't
   already have it.
2. Clone this repo and build:
   ```sh
   git clone https://github.com/MosesDSI/primitive-reflexivity-lean4.git
   cd primitive-reflexivity-lean4
   lake exe cache get   # fetches prebuilt Mathlib .olean files — avoids compiling Mathlib from source
   lake build
   ```
   `elan` will automatically install the pinned Lean toolchain (`v4.33.1`, see
   [`lean-toolchain`](lean-toolchain)) the first time you run `lake`.
3. A clean exit with `Build completed successfully` and no `error:` lines is the verification.
   Two harmless linter warnings are expected (a deprecated-lemma-name notice and a style
   suggestion) — neither is a proof gap.

Alternatively, trust the CI badge above: it runs this exact build on a fresh GitHub Actions runner
on every push.

## Structure

- `PrimitiveReflexivity/Foundations.lean` — the formalization (the deliverable).
- `PrimitiveReflexivity/Basic.lean` — unused scaffold file from `lake new`.
- `Theorems_Original_and_Adjustments.md` — original theorem code + full adjustment log.
- `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` — build summary / verification record.
- `ACKNOWLEDGMENTS.md` — authorship and the human–AI formalization pipeline (Jonathon Pearson's
  paper → Gemini's initial Lean translation → Claude Code's environment setup and proof repair),
  plus a note on what "verified" does and doesn't establish.
- `lakefile.toml` / `lean-toolchain` — pin the exact Lean and Mathlib versions used.

## License

MIT — see [`LICENSE`](LICENSE).
