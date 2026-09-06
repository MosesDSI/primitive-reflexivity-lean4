# Theta__0_Photon

A Lean 4 + Mathlib extension of the main formalization's `metric_independence` pattern,
built on the reading "0 is not a number, it's a process." Unlike `R3_bare_lean/` and
`Section_VI_Incommensurability/`, this project uses Mathlib and `lake build` — same pinned
toolchain (`v4.33.1`) and Mathlib revision (`0df444a3`) as the top-level formalization above.

## What's proved

**`Theta0Photon/Basic.lean`** — a `Node`/`NodeMetric` diagonal-collapse theorem, in the same
shape as the top-level `metric_independence`:
- `zero_is_not_a_coordinate` — for any metric where `dist x x = 0`, a `P`-decorated relation
  at the diagonal collapses to the bare relation, given `P` holds at `0`.
- `off_diagonal_dist_ne_zero` / `dist_eq_zero_iff_R` — extend this to *strict* metrics (every
  off-diagonal pair has strictly positive distance): zero distance then exactly characterizes
  the relation, not just implies it on the diagonal.

**`Theta0Photon/Statistics/CenteredKernel.lean`** — a real-valued statistical analogue built
independently from the theorems above (see Scope note below):
- `finrank_centeredSubspace` — the centered subspace (kernel of the sum map on `Fin N → ℝ`)
  has dimension exactly `N - 1`: projecting onto the mean costs one degree of freedom, for
  general `N` (proved via Mathlib's `Module.Dual.finrank_ker_add_one_of_ne_zero`).
- `sample_space_direct_sum` — the diagonal (constant-vector) subspace and the centered
  subspace are complementary (`IsCompl`): every sample decomposes uniquely into a mean part
  and a zero-sum part.
- `diagonal_subspace_sum_sq_deviation_zero` / `diagonal_subspace_pairwise_dist_zero` — any
  sample lying in the diagonal subspace has zero variance and every pair of its coordinates
  is equal: the diagonal carries no dispersion.

Zero `sorry` across both files.

## Scope

The parallel between the two files above is structural, not a literal shared Lean
dependency: `NodeMetric.dist` is `Nat`-valued, `Sample` is `ℝ`-valued, and neither file's
theorems appear in the other's proof term — confirmed by inspection (`#print axioms`) rather
than assumed from the shared "diagonal" language.

`Main.lean` also contains `Photon`, `Superposition`, and `EncryptedPacket` — these are the
same `Process` proof term (`zeroProcess`) under different names, i.e. a naming/interpretation
layer over `zero_is_not_a_coordinate`, not independently-proved claims about physical photons
or superposition.

## Building

From this directory:
```sh
lake exe cache get
lake build
```
CI (`.github/workflows/lean_action_ci.yml`) runs the same build on every push via
`leanprover/lean-action`.
