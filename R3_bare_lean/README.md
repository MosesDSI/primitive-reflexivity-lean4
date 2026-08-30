# Axiomatic Invariance & Dual-Clock Test Harness

Dependency-free Lean 4 verification files for "Foundations of Primitive
Reflexivity." Everything in this directory type-checks against bare Lean 4
alone — no `import Mathlib` anywhere — and is checked directly with
`lean <file>.lean`, not through `lake build`. It is pinned to the same
toolchain as the main project (`leanprover/lean4:v4.33.1`, see
`../lean-toolchain`) but is intentionally kept outside that project's
`lean_lib` target, so it never affects — and is never affected by — the
Mathlib-dependent `Foundations.lean` build.

## Purpose

Two questions, both about the *logical shape* of a claim independent of any
specific mathematical domain, are tested here:

1. **R3 — A-Metric Independence** (`R3_*.lean`): does a relation `R`,
   decorated with an external structure's diagonal value, stay logically
   equivalent to plain `R` on the diagonal `(x, x)`? Tested across three
   independent structural axes — metric (`dist_self`), order (`le_refl`),
   algebraic (`op_zero`) — plus a tautological control (no real structure,
   shows the trivial case) and a decorated control (an assumed hypothesis,
   not a derived one).
2. **Section VI — Dual-Clock Engine** (`Section_VI_dual_clock.lean`): is the
   ontological angle-as-phase-drift predicate (`PhaseDriftMatch`) a real,
   discriminating predicate, or does it hold vacuously for any input?

## Verification tier — what is and isn't established here

Each file is independently checked with `lean <file>.lean`; a clean run
means 0 errors, and `#print axioms` (where present) confirms no `sorryAx`
and no axioms beyond, or in the R3 files' case none at all.

**What's confirmed, per file:**
- `R3_tautological.lean` — compiles; the only file with a warning
  (`extra` unused), which is the intended demonstration that a purely
  tautological version has no structural content.
- `R3_decorated.lean`, `R3_metric.lean`, `R3_algebraic.lean`,
  `R3_order.lean` — compile clean, 0 axioms. Confirmed by reading the
  proof terms (not just the compile result) that each uses exactly one
  reflexivity-shaped axiom from its structure (`dist_self` / `le_refl` /
  `op_zero`) and never touches the richer axioms also present
  (`dist_symm`, `dist_triangle`, `le_trans`, `le_antisymm`).
- `Section_VI_dual_clock.lean` — compiles clean under both default
  elaboration and `set_option autoImplicit false`. `PhaseDriftMatch` is
  confirmed non-vacuous: provable for a genuinely calibrated instance
  (3 `rotate_step`s from `0` reaching target `3`, with `Phase := Nat`,
  `rotate_step := (·+1)`), disprovable for a genuinely mismatched instance
  (target `7`), and the earlier loose-existential form's vacuity attack
  (fabricating a proof for an arbitrary unrelated target) fails against
  this definition with a real type-mismatch error, not merely "isn't
  attempted."

**What this tier does not establish:** none of these files reference or
depend on the real mathematical objects used in the main
`Foundations.lean` suite (`ℝ`, `Real.sqrt`, `Circle`, groups). The
`BifurcatedState` / `AxialRotation` structures here are abstract —
verification confirms `PhaseDriftMatch` behaves correctly as a logical
predicate over *any* type satisfying `AxialRotation`, not that it
correctly models any specific physical or geometric clock. Connecting
this predicate to a concrete Polar/Axial instantiation tied to the paper's
actual geometry is separate, not-yet-done work.

## Reproducing

See `../R3_Lean_Testing_Reproduction_Guide.md` for the bare-Lean-4 setup
(no `lake`/`elan` toolchain resolution needed — pull the release directly)
and per-file expected output.
