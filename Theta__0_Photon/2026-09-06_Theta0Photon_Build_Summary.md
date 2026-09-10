# Theta0Photon Build Summary

**Date:** 2026-09-06
**Project:** `Theta__0_Photon` (subfolder of `PrimitiveReflexivity`)
**Toolchain:** Lean 4 with the project-pinned toolchain

## Objective

Connect the Theta0Photon scratch project to the already-verified R3 metric formulation from the PrimitiveReflexivity project, without adding arbitrary axioms for the central result.

The relevant verified pattern is the R3 metric theorem:

```lean
def MetricDecorated (R : N → N → Prop) (d : Metric N)
    (P : Nat → Prop) (x y : N) : Prop :=
  R x y ∧ P (d.dist x y)

theorem metric_independence
    (R : N → N → Prop) (d : Metric N) (P : Nat → Prop)
    (hgate0 : P 0) :
    ∀ x, MetricDecorated R d P x x ↔ R x x
```

## Initial State

`Main.lean` attempted to define a process and prove:

```lean
M x x = 0 ↔ x R x
```

However, the project did not define the required `Node`, `Metric`, `Process`, or relation infrastructure. It also referred to missing declarations `Axiom_R3_fwd` and `Axiom_R3_inv`.

The first version also used the Unicode lambda arrow `→` in a lambda expression. Lean expects `=>` there.

The name `Zero` also conflicted with an existing Lean declaration, and the resulting type mismatch affected `Photon`, `Superposition`, and `EncryptedPacket`.

## Problems Fixed

### 1. Missing foundational types

Added a concrete node type:

```lean
structure Node where
  id : Nat
```

Added the primitive relation:

```lean
def R (x y : Node) : Prop := x = y
```

The relation is kept as an ordinary function, matching the verified R3 implementation. An attempted infix notation was removed because it conflicted with using `R` as a relation parameter in definitions.

### 2. Arbitrary metric axioms removed

The original scratch project introduced these assumptions:

```lean
axiom Axiom_R3_fwd ...
axiom Axiom_R3_inv ...
```

These were removed. They made the desired theorem an assumption rather than a derivation, especially because they claimed a bidirectional relationship between every metric's diagonal and reflexivity.

### 3. Metric made into an explicit structure

Added `NodeMetric`:

```lean
structure NodeMetric (N : Type) where
  dist : N → N → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
```

The name `NodeMetric` avoids a collision with an existing Lean declaration named `Metric` in this environment.

Only `dist_self` is needed for the diagonal theorem. Symmetry and the triangle inequality remain present because they describe the intended metric structure, but the proof does not pretend to use properties it does not need.

### 4. Metric decoration added

Added:

```lean
def MetricDecorated (R : Node → Node → Prop) (M : NodeMetric Node)
    (P : Nat → Prop) (x y : Node) : Prop :=
  R x y ∧ P (M.dist x y)
```

This expresses the external metric information as a decoration of the underlying relation.

### 5. Central theorem corrected and proved

`zero_is_not_a_coordinate` now states:

```lean
theorem zero_is_not_a_coordinate :
  ∀ (M : NodeMetric Node) (P : Nat → Prop),
  P 0 → ∀ x : Node, MetricDecorated R M P x x ↔ R x x
```

The proof proceeds as follows:

1. Unfold `MetricDecorated`.
2. Rewrite `M.dist x x` to `0` using the metric's explicit `dist_self` field.
3. From the decorated relation, project the `R x x` component.
4. Given `R x x`, pair it with the assumed gate condition `P 0`.

This is the same mechanism as the verified `metric_independence` theorem in the R3 guide. The metric does not disappear by an unexplained compiler preference; the proof explicitly invokes the diagonal law `dist_self`.

### 6. Process definitions retained

The process is now:

```lean
def Process := ∀ x : Node, R x x
```

`zeroProcess` is defined by reflexivity (`rfl`), and the following names remain aliases of that process:

```lean
def Photon : Process := zeroProcess
def Superposition : Process := zeroProcess
def EncryptedPacket : Process := zeroProcess
```

`Zero` was renamed to `zeroProcess` because `Zero` is already declared by Lean.

### 7. Lambda syntax corrected

The original expression:

```lean
λ (x : Node) → ...
```

was changed to Lean's lambda syntax:

```lean
λ (x : Node) => ...
```

## Files Changed

- `Theta0Photon/Basic.lean`
  - Added `Node`, `R`, `NodeMetric`, `Process`, and `MetricDecorated`.
  - Removed the arbitrary R3 axioms.

- `Main.lean`
  - Renamed `Zero` to `zeroProcess`.
  - Corrected lambda syntax.
  - Replaced the assumed metric equivalence with the verified decorated-metric theorem.

## Verification

The following commands succeeded:

```powershell
lake build Theta0Photon
lake env lean Main.lean
```

There are no compilation errors and no `sorry` proofs were introduced.

Lean reports stylistic warnings because `zeroProcess`, `Photon`, `Superposition`, and `EncryptedPacket` have proposition-valued types and are declared with `def`. These warnings do not indicate proof failures. (Resolved in Part 2 below.)

## Meaning of the Result

The formal result establishes a precise logical claim:

> At the diagonal, a metric decoration whose predicate holds at zero is equivalent to the underlying reflexive relation.

In other words, the metric contributes no additional information at `x` related to itself, because `dist x x = 0`.

The formalization does **not** independently prove the broader physical or ontological interpretation that a photon is literally zero, or that zero is not a number. Those ideas are currently represented as names and comments. To formalize them further, they would need precise mathematical definitions and separately stated theorems.

## Next Formalization Opportunities

Potential next steps are:

1. Replace `Node.id : Nat` with the intended node-space model.
2. Define a meaningful process transition or evolution relation.
3. State the photon claim as a precise property rather than an alias of `zeroProcess`.
4. Add a small example metric and prove that it satisfies `NodeMetric`.
5. Add an axiom audit or `#print axioms` check if the project grows beyond this foundational theorem.

---

## Part 2: `Theta0Photon.Statistics.CenteredKernel` and strict off-diagonal metrics

Later the same day, the project was extended with a real-valued statistical
counterpart to the `Node`/`NodeMetric` diagonal result above, plus a strict
(non-degenerate) variant of the metric itself. This section documents that
work and the final hygiene pass, so the scope and verification method of
each new theorem is on record rather than only asserted in chat.

### Mathlib dependency added

`Theta__0_Photon` originally had no Mathlib dependency (`lake-manifest.json`
had `"packages": []`), so nothing requiring real numbers or linear algebra
could compile. Rather than a fresh `lake update` (re-downloading and
rebuilding all of Mathlib), `.lake/packages` was linked via a directory
junction to the already-built copy in the sibling `PrimitiveReflexivity`
project (same pinned toolchain, `v4.33.1`), and `lakefile.toml` was given
the matching `[[require]] name = "mathlib"` block. `lake-manifest.json` was
copied from the sibling and renamed. This reuses the existing build rather
than duplicating a multi-gigabyte dependency tree.

### `Sample` had to become `abbrev`, not `def`

`Sample (N : ℕ) := Fin N → ℝ` was originally a plain `def`. This is fine as
long as nothing ever needs algebraic typeclass instances (`Module`,
`AddCommMonoid`, ...) *on* `Sample N` itself — indexing (`s i`) never
triggers instance search. It breaks the moment a proof destructures a
`Submodule` membership witness into an explicit scalar multiple typed at
`Sample N` (as `diagonal_subspace_pairwise_dist_zero` and
`diagonal_subspace_deviation_zero` both need to): Lean's typeclass search
does not unfold plain semireducible `def`s, so it failed with
`failed to synthesize instance Module ℝ (Sample N)`. Fixed by declaring
`Sample` as `abbrev`, which is transparent to instance search. This is a
correction, not a workaround — `Sample` was always meant to be nothing but
a readable alias for `Fin N → ℝ`.

### `CenteredKernel.lean`: theorems added, in dependency order

All proved directly, zero `sorry`, axiom-checked individually via
`#print axioms` against the local Mathlib source (not assumed from the
lemma name alone):

- `Sample`, `sampleMean`, `deviation`, `deviations_sum_zero` — the sample
  mean and centered-deviation machinery, with `deviations_sum_zero` proved
  by explicitly instantiating `Finset.sum_sub_distrib (f := s) (g := fun _ => sampleMean s)`
  rather than plain `rw [Finset.sum_sub_distrib]`, which fails outright: `rw`'s
  `kabstract` cannot resolve the higher-order pattern when one side of the
  subtraction (`sampleMean s`) does not mention the bound index.
- `sumMap`, `CenteredSubspace`, `DiagonalSubspace`, `D1`, `D2`,
  `square_diagonals_orthogonal`, `d2_in_centered_subspace`,
  `sample_decomp_two`, `two_cell_direct_sum` — the `N = 2` illustration.
  `square_diagonals_orthogonal`/`d2_in_centered_subspace` originally used
  `by decide` in a draft script; `decide` cannot evaluate `ℝ` equality
  (stuck kernel reduction), so both use `norm_num` instead.
- `sumMap_ne_zero` and `finrank_centeredSubspace : Module.finrank ℝ (CenteredSubspace N) + 1 = N` —
  the general-`N` rank-nullity result (the actual "N − 1 degrees of freedom"
  claim; the `N = 2` case above only illustrates it). Proved via
  `Module.Dual.finrank_ker_add_one_of_ne_zero`, located by reading the
  pinned Mathlib source directly (`Mathlib/LinearAlgebra/Dual/Lemmas.lean`)
  rather than guessed.
- `diagonalSubspace_eq_span : DiagonalSubspace N = Submodule.span ℝ {fun _ => 1}` —
  needed first: `DiagonalSubspace` was defined as the span of the raw set
  `{v | ∃ c, v = fun _ => c}`, and that set is already closed under the
  submodule operations, so its span is exactly the span of one generator.
- `sample_space_direct_sum : IsCompl (DiagonalSubspace N) (CenteredSubspace N)` —
  via `Module.Dual.isCompl_ker_of_disjoint_of_ne_bot`, reusing
  `sumMap_ne_zero`; disjointness and `DiagonalSubspace N ≠ ⊥` proved by hand
  from the span characterization above.
- `diagonal_subspace_pairwise_dist_zero (hs : s ∈ DiagonalSubspace N) (i j) : s i - s j = 0` —
  the requested pairwise-coordinate result: a diagonal sample is a single
  repeated value.
- `diagonal_subspace_deviation_zero (hs : s ∈ DiagonalSubspace N) (i) : deviation s i = 0` —
  the same fact restated in terms of the file's own mean-deviation
  machinery, so it is the actual zero-variance statement, not just an
  analogous one.
- `diagonal_subspace_sum_sq_deviation_zero (hs : s ∈ DiagonalSubspace N) : ∑ i, deviation s i ^ 2 = 0` —
  the sum-of-squared-deviations form of "the diagonal subspace has zero
  variance," a one-line corollary of the previous theorem.

**Explicitly not claimed:** these are the real-valued statistical analogue
of `zero_is_not_a_coordinate`, not a formal consequence of it. `NodeMetric.dist`
is `Nat`-valued; `Sample` is `ℝ`-valued; there is no shared type, instance,
or import between `Main.lean`'s `Node`/`NodeMetric` chain and
`CenteredKernel.lean`. The parallel ("an external decoration is forced to
its trivial value on the distinguished degenerate locus") is structural,
stated as a doc comment in the file, and was checked to not appear in
either theorem's `#print axioms` ancestry.

### `Basic.lean`: strict metrics

Added, without modifying the `NodeMetric` structure itself (so
`zero_is_not_a_coordinate` keeps holding for non-strict metrics too):

```lean
def OffDiagonal (x y : Node) : Prop := ¬ R x y

def NodeMetric.Strict (M : NodeMetric Node) : Prop :=
  ∀ x y, OffDiagonal x y → 0 < M.dist x y

theorem off_diagonal_dist_ne_zero {M : NodeMetric Node} (hM : M.Strict)
    {x y : Node} (hxy : OffDiagonal x y) : M.dist x y ≠ 0 := by
  have h := hM x y hxy
  omega

theorem dist_eq_zero_iff_R {M : NodeMetric Node} (hM : M.Strict) (x y : Node) :
    M.dist x y = 0 ↔ R x y := by
  constructor
  · intro h0
    exact Classical.byContradiction fun hne => off_diagonal_dist_ne_zero hM hne h0
  · intro hR
    have hxy : x = y := hR
    rw [hxy]
    exact M.dist_self y
```

`dist_eq_zero_iff_R` is the sharper result: it is not enough that off-diagonal
distances are positive on their own — the theorem shows positivity is a
*complete* test for being off-diagonal (contrapositive of `off_diagonal_dist_ne_zero`,
combined with the existing `dist_self` for the converse direction). The
zero-distance set of a strict metric is exactly the diagonal, no more and
no less, which is the precise sense in which "metric decorations only
introduce non-trivial information outside the diagonal."

### Hygiene / lint audit

- **Unused imports:** `open BigOperators FiniteDimensional LinearMap` in
  `CenteredKernel.lean` was dead — every use in the file is already fully
  qualified (`Module.finrank`, `LinearMap.ker`, `Module.Dual....`). Verified
  by removing the line and rebuilding clean, not by inspection alone. The
  four `import Mathlib...` lines were each individually confirmed load-bearing.
  `Basic.lean` has no imports. `lake shake` (Mathlib's own unused-import
  tool) was tried first but errors `lake shake only works with modules` on
  every invocation in this environment, including against the sibling
  `PrimitiveReflexivity` project with no arguments — the tool itself is
  non-functional here, not just picky about this project's shape.
- **Namespace collisions:** none. Grepped the sibling `PrimitiveReflexivity`
  project's `Foundations.lean`, `R3_bare_lean`, and `Section_VI_Incommensurability`
  for every top-level name used here (`R`, `Node`, `Process`, `Sample`,
  `sumMap`, `CenteredSubspace`, `DiagonalSubspace`) — zero matches. The two
  projects share the `PrimitiveReflexivity` namespace name by coincidence
  but are never in the same import closure (`Theta__0_Photon` only junction-links
  the sibling's `.lake/packages`, i.e. Mathlib and its dependencies, never
  the sibling's own compiled library), and this project's content sits one
  level deeper, under `PrimitiveReflexivity.Statistics`.
- **Linter warnings:** `Main.lean` had 4 pre-existing warnings — an
  unreferenced lambda binder on `zeroProcess`, and `zeroProcess`/`Photon`/
  `Superposition`/`EncryptedPacket` declared with `def` despite being
  `Prop`-valued. Fixed: binder renamed `x` → `_x`; all four switched from
  `def` to `theorem`. Re-verified by `#print axioms` after the change (all
  five report "does not depend on any axioms," unchanged from before the
  rename, confirming the edit didn't alter what was actually proved).

### Verification

```powershell
lake build Theta0Photon Main
```
completes with **zero warnings and zero errors** across both targets (the
`theta__0_photon:exe` link target is a separate, pre-existing, unrelated
failure — `Main.lean` has no `def main`, so the linker cannot find
`WinMain`; this is expected for a proof file and was never in scope here).

Every new theorem was checked individually with `#print axioms` against
this project's own build (not assumed from context):

| Theorem | Axioms |
|---|---|
| `zero_is_not_a_coordinate` | none |
| `finrank_centeredSubspace` | `propext`, `Classical.choice`, `Quot.sound` |
| `sample_space_direct_sum` | `propext`, `Classical.choice`, `Quot.sound` |
| `diagonalSubspace_eq_span` | `propext`, `Classical.choice`, `Quot.sound` |
| `diagonal_subspace_pairwise_dist_zero` | `propext`, `Classical.choice`, `Quot.sound` |
| `diagonal_subspace_deviation_zero` | `propext`, `Classical.choice`, `Quot.sound` |
| `diagonal_subspace_sum_sq_deviation_zero` | `propext`, `Classical.choice`, `Quot.sound` |
| `off_diagonal_dist_ne_zero` | `propext`, `Quot.sound` |
| `dist_eq_zero_iff_R` | `propext`, `Classical.choice`, `Quot.sound` |

No `sorryAx`, no project-defined axioms, anywhere.

## Follow-up: git structure

`Theta__0_Photon` was discovered mid-session to have its own nested `.git`
(one throwaway "Initial commit", no remote) — a side effect of pulling the
`PrimitiveReflexivity` repo content into VS Code for agent context, not a
deliberate `git init`. Per user decision, the nested `.git` was removed and
`Theta__0_Photon` was folded into the outer `PrimitiveReflexivity` repo as
a plain subfolder, consistent with `R3_bare_lean` and
`Section_VI_Incommensurability`. Committed locally in `PrimitiveReflexivity`
(`c9dcbc7`, message: "feat(statistics): verify diagonal zero-variance and
strict off-diagonal metric theorems in Lean 4"); not pushed to any remote.
