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

**Start here for the full picture:**
[**`Foundations_of_Primitive_Reflexivity_Verified_Edition.md`**](Foundations_of_Primitive_Reflexivity_Verified_Edition.md)
walks every theorem across *all four* project trees in this repo — this file, `R3_bare_lean/`,
`Section_VI_Incommensurability/`, and the companion `Theta__0_Photon/` project — as one narrative,
with a live link from each theorem straight into the `.lean` file and declaration that proves it.
This root README covers only `Foundations.lean` itself.

## What's proved

All theorems live in [`PrimitiveReflexivity/Foundations.lean`](PrimitiveReflexivity/Foundations.lean).

| Theorem | Statement |
|---|---|
| `reflexive_minimality` | The diagonal of a locally-reflexive `ℛ` is contained in every pointwise-reflexive relation `S`: `x ℛ x → x S x`. |
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
- [`PrimitiveReflexivity/Discrete/OrderObstruction.lean`](PrimitiveReflexivity/Discrete/OrderObstruction.lean)
  — an order-theoretic obstruction to rational retraction (no order-preserving map from a
  number system back onto ℚ can fix every rational once that system contains a point
  incommensurable with ℚ), instantiated concretely as a from-scratch, kernel-verified
  certified ordered field `QS` modeling ℚ(√2) — field laws, global order, and density, all
  proved in **bare Lean 4, no Mathlib**, then wired into this project's own `lake build`
  (part of the `PrimitiveReflexivity` library target, currently 2748/2748 jobs). Verified
  trust footprint: `[propext, Classical.choice, Quot.sound]` — the same standard base as
  the rest of this repo, zero `sorryAx`. See
  [`2026-09-24_OrderObstruction_Density_and_Integration.md`](2026-09-24_OrderObstruction_Density_and_Integration.md)
  and its companion build summaries for the full development history.
- [`PrimitiveReflexivity/Discrete/HarmonicCenter.lean`](PrimitiveReflexivity/Discrete/HarmonicCenter.lean)
  — discrete harmonic centers: a symmetric center point for the interval `{1,...,2k+1}`, and
  (for `k=10`) the mod-3 partition class containing that center has the strictly smallest total
  distance sum among the three classes.
- [`PrimitiveReflexivity/Geometry/SquareUnfolding.lean`](PrimitiveReflexivity/Geometry/SquareUnfolding.lean)
  — the boundary of a square unfolds isometrically onto an interval of length `4s`, with edge
  lengths and corner adjacency preserved exactly.
- `Theorems_Original_and_Adjustments.md` — original theorem code + full adjustment log.
- `2026-08-28_PrimitiveReflexivity_Lean4_Formalization.md` — build summary / verification record.
- `ACKNOWLEDGMENTS.md` — authorship and the human–AI formalization pipeline (Jonathon Pearson's
  paper → Gemini's initial Lean translation → Claude Code's environment setup and proof repair),
  plus a note on what "verified" does and doesn't establish.
- [`A_Comment_from_Claude/`](A_Comment_from_Claude/README.md) — Claude's own first-person
  engineering-report archive: retrospectives on the coding expertise and ingenuity behind builds
  in this repo, written at Jonathon's request. One dated file per build.
- `lakefile.toml` / `lean-toolchain` — pin the exact Lean and Mathlib versions used.

Two further directories extend this formalization in **bare Lean 4 — no
Mathlib, no `lake build`, not part of the verification above**. Each has
its own `README.md` documenting scope and verification tier:
- `R3_bare_lean/` — Axiom R3 (A-Metric Independence) across metric, order,
  and algebraic structural axes, plus the Section VI dual-clock
  (`PhaseDriftMatch`) ontological angle definition.
- `Section_VI_Incommensurability/` — a from-scratch (no Mathlib) proof that
  the Polar and Axial clocks share no common rational measure, connected
  directly to `PhaseDriftMatch`.

A third directory, [`Theta__0_Photon/`](Theta__0_Photon/README.md), is its own Lean 4 + Mathlib
project — same pinned toolchain and Mathlib revision as this repo — that has grown well past its
original `metric_independence` diagonal-collapse / statistical-analogue starting point: it now also
proves the `ℚ(√2,√3)` field tower and its Klein four-group of automorphisms, the "Phantom Middle"
symmetry that fixes exactly the product `√2·√3` (and is the unique non-identity symmetry doing so),
a triadic-closure result and, for the pair `(2,3)` only, a bridge showing that symmetry fixes the
product coordinate and negates the sum coordinate of the two triadic states (this repo's own
mediator-defect setting),
a chiral-sign/orientation law, and a countable/uncountable operational-orthogonality result. See its
own `README.md` for the full theorem-by-file ledger, or the narrative doc linked above for all of it
walked together with this project's theorems.

## License

MIT — see [`LICENSE`](LICENSE).
