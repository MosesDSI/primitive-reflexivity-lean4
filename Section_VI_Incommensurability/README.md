# Section VI/VIII: Polar/Axial Incommensurability

Dependency-free Lean 4 files (no Mathlib) proving that the Polar and Axial
clocks — the dual-clock bifurcation formalized in
`../R3_bare_lean/Section_VI_dual_clock.lean` — share no common rational
measure, and connecting that fact directly to `PhaseDriftMatch`, not just
placing it nearby.

Each file compiles standalone via `lean <file>.lean`, following this
project's bare-Lean convention (see `../R3_bare_lean/README.md`).

## Files

- **`Polar_Axial_Incommensurability.lean`** — the core number-theoretic
  result. Reconstructs, from first principles over `Nat` (no `Real`, no
  `Irrational`), the classical parity/infinite-descent proof that no
  naturals `p, q` (`q ≠ 0`) satisfy `p² = 2q²` — the bare-arithmetic form of
  "√2 is irrational." `polar_axial_incommensurable` applies this directly:
  no finite Polar/Axial tick pair can satisfy the diagonal-closure ratio.
  Mirrors Section VII's `manhattan_step`/`diagonal_step`/
  `no_common_rational_measure` pattern (`Foundations.lean`), rebuilt without
  Mathlib.

- **`Axial_Divergence_Theorem.lean`** — the connecting result.
  `PhaseDriftMatch` (Section VI's non-vacuous angle-as-phase-drift
  predicate) is not merely compatible with the incommensurability proof —
  it's structurally tied to it: for any fixed natural per-tick Axial
  rotation, `PhaseDriftMatch` certifies exactly which phase is reached
  after `n` Polar ticks, and the same descent lemma behind
  `polar_axial_incommensurable` proves that certified phase can never
  satisfy the √2-closure condition, for any rotation step whatsoever.

## Verification tier — what's confirmed, and what this does and doesn't establish

**Confirmed, per file:**
- `Polar_Axial_Incommensurability.lean` — compiles clean; `#print axioms`
  on `polar_axial_incommensurable` shows only `[propext, Quot.sound]`, no
  `sorryAx`, no `Classical.choice`. A control check (ratio 4, `m²=4n²`,
  which *is* rational since `√4=2`) confirms real solutions exist there —
  the descent proof is specific to ratio 2, not a vacuous always-false
  statement about any equation of this shape.
- `Axial_Divergence_Theorem.lean` — compiles clean; same axiom purity on
  `axial_clock_never_closes_the_diagonal_gap`. The "reached phase" half is
  independently confirmed non-vacuous with a concrete instance
  (`c=3, n=2` genuinely reaches phase `6`, checked directly) — `Phase-
  DriftMatch` is doing real work here, not standing in as an unconstrained
  placeholder.

**What this tier does not establish:** the Axial rotation modeled here
(`rotate_step := (·+c)` for a fixed natural `c`) is a linear, constant-step
rotation — chosen because it is the simplest instance whose reachable value
after `n` ticks is exactly `n·c`, letting the connecting proof reuse
`no_sqrt2_aux` directly. It does not model, and makes no claim about, a
continuous or genuinely circular (mod-2π-style) rotation — that remains
future work, and per the design discussion in this session would require
`Real`/`Circle` machinery from Mathlib (the main `Foundations.lean`
project's `irrational_pi`), not bare Lean.

## Reproducing

Same setup as `../R3_bare_lean/` — see
`../R3_Lean_Testing_Reproduction_Guide.md` §1 for the bare-Lean-4 toolchain
pull (no `lake`/`elan` resolution needed).
