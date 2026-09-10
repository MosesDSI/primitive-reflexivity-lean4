# Theta__0_Photon

A Lean 4 + Mathlib extension of the main formalization's `metric_independence` pattern,
built on the reading "0 is not a number, it's a process." Unlike `R3_bare_lean/` and
`Section_VI_Incommensurability/` (in the parent `PrimitiveReflexivity/` project), this
project uses Mathlib and `lake build` — same pinned toolchain (`v4.33.1`) and Mathlib
revision (`0df444a3`) as the top-level formalization.

**Note on scope:** `Theta0Photon` and `PrimitiveReflexivity` are two separate Lake
projects sharing Mathlib via a directory junction, with no compiled-library dependency
edge between them. Where a theorem here overlaps with one proved in
`PrimitiveReflexivity/Foundations.lean`, it has been re-derived independently against
this project's own pinned toolchain rather than imported — noted explicitly at each
such point below, not silently assumed.

## Framework Overview

The framework's central move — laid out in full in
[`Theta0Photon/Documentation/CoreAxioms.md`](Theta0Photon/Documentation/CoreAxioms.md),
Section V, "Core Axioms: The Triadic Substrate and the Lossy Compression of Classical
ℕ_classical" — is to define the natural numbers strictly as the full 3-component state:

```
ℕ ≡ { (n, √n, n²) | n ∈ ℕ_classical }
```

read as a **polar coordinate** (the discrete count `n`), an **axial mediator** (the
continuous scale `√n`), and a **planar boundary** (the potential/volumetric capacity
`n²`). `ℕ_classical` names Mathlib's own `Nat` in this notation — the indexing set the
triadic bundle is built over. On this framework's own stipulated definition, `ℕ`
(the full triadic state) and `ℕ_classical` (the bare count alone) are different objects,
and the classical 1D natural number line is a lossy 1D projection of the 3D triadic
manifold: it keeps `n` and discards the other two coordinates.

This is the framework's own definition, stated as such — it is not a claim that
`ℕ_classical` (Mathlib's `Nat`) is internally inconsistent or incomplete as *that* type,
and nothing in this repository asserts that; `Nat.add` remains exactly what Mathlib
defines it to be, untouched by anything here. What *is* machine-checked, precisely, is:

- Bundling `n` with `√n` and `n²` (`TriadicNat`) preserves an exact, zero-residue
  relationship under componentwise **multiplication**, but not under componentwise
  **addition** — addition produces a specific, provably positive, nonzero real-valued
  gap (`mediator_defect`) between the naive componentwise sum and what a valid bundled
  state at `n+m` would require.
- This asymmetry is a fact about the *bundle and the two componentwise operations
  defined on it*, not a statement about `Nat.add` itself, which is untouched by any of
  this and remains exactly what Mathlib defines it to be.

See the module docstring of
[`TriadicClosure.lean`](Theta0Photon/Algebra/TriadicClosure.lean) and the "On the scope
of this cross-reference" note in `CoreAxioms.md` for the exact boundary of what is and
isn't claimed.

## Verification Ledger

Every theorem below is machine-checked with **zero `sorry`**, confirmed via `#print
axioms` at the time each file was built (or re-confirmed at time of writing). Current
full-library build: **`lake build Theta0Photon` and `lake build Main` — 2484/2484 jobs
each, clean, zero warnings** (re-confirmed at time of writing).

| File | Key results | Method | Axiom trust base |
|---|---|---|---|
| [`GroundAxiom.lean`](Theta0Photon/Algebra/GroundAxiom.lean) | `triadic_no_rational_root`, `triadic_ground_irreducible` — `X²−n` is irreducible over `ℚ` for any non-square `n` | `irreducible_of_degree_le_three_of_not_isRoot` + `Rat.sqrt_natCast` | `[propext, Classical.choice, Quot.sound]` |
| [`FieldTower.lean`](Theta0Photon/Algebra/FieldTower.lean) | `sqrt2_finrank`/`sqrt3_finrank` (degree 2 each), `sqrt3_notMem` (√3 ∉ ℚ⟮√2⟯), `sqrt2_sqrt3_finrank` — `[ℚ⟮√2,√3⟯:ℚ] = 4` | Explicit-basis route; `IntermediateField.algHomAdjoinIntegralEquiv`, tower law `finrank_mul_finrank` | `[propext, Classical.choice, Quot.sound]` |
| [`GaloisGroup.lean`](Theta0Photon/Algebra/GaloisGroup.lean) | `sigma_K`, `tau_K`, `phantom_middle := sigma_K.trans tau_K`; `card_Gal_eq_four`; `instance IsGalois ℚ K`; `instance IsKleinFour (K ≃ₐ[ℚ] K)`; `galoisKleinFourEquiv_phantom_middle` | Explicit `AlgEquiv` construction via `IntermediateField.equivOfEq` (avoiding the `AlgEquiv.refl` auto-closing pitfall — see file docstring); `IsGalois.of_card_aut_eq_finrank` | `[propext, Classical.choice, Quot.sound]` |
| [`ChiralSign.lean`](Theta0Photon/Geometry/ChiralSign.lean) | `chiral_sign_law` (= Mathlib's `Matrix.det_permute`, restated); `transposition_flips_orientation`; `canonicalOrbitMatrix_det = -21` reproved inside Lean's kernel | `Matrix.det_permute`, `Matrix.det_fin_three`, exhaustive `decide` over `S₃`'s 6 elements for `fin3_isOdd_iff_isSwap` | `[propext, Classical.choice, Quot.sound]` |
| [`Incommensurability.lean`](Theta0Photon/SetTheory/Incommensurability.lean) | `isEmpty_structurePreserving_of_operationallyOrthogonal` (general, any predicate); `isEmpty_equiv_K_real` — no bijection `K ≃ ℝ` exists, `K = ℚ⟮√2,√3⟯` from the field tower | Cardinality argument via `Function.Injective.countable`/`Uncountable`; `K`'s countability transported from `finrank ℚ K = 4` via `Module.finBasis` | `[propext, Classical.choice, Quot.sound]` |
| [`TriadicClosure.lean`](Theta0Photon/Algebra/TriadicClosure.lean) | `mediator_defect_positive` (re-derived from `PrimitiveReflexivity/Foundations.lean`, 2026-08-28); `triadic_multiplication_closed` (exact); `triadic_addition_not_closed`; `π`, `projection_commutes_on_n`, `correction_identity` | AM-GM-style squaring argument; `Real.sqrt_mul`; direct `rw`/`ring` on the exact correction quantity | `[propext, Classical.choice, Quot.sound]` |
| [`UniquenessTest.lean`](Theta0Photon/Algebra/UniquenessTest.lean) | `const_one_multiplicative_closure`, `const_one_additive_residue`, `const_one_satisfies_both_conditions` — the constant function `f=1` satisfies exact multiplicative closure and strictly positive additive residue; flagged in the file itself as a degenerate, scale-collapsed case (no dependence on `n`, no operational scaling capacity), not a rival mediator to `√n` | `norm_num` | `[propext, Classical.choice, Quot.sound]` |
| [`CoreAxioms.md`](Theta0Photon/Documentation/CoreAxioms.md) | Documentation module cross-referencing every theorem above to the framework's stated axioms, including an explicit scope note on what the `π` projection does and does not establish | — | — |

**A correction folded into this milestone:** `UniquenessTest.lean` originally also
carried an `n³` "counterexample." That theorem in fact proved a strictly *negative*
residue for `n³`, which is the opposite of the positive-residue condition being tested
— it did not establish what the file claimed, and has been removed rather than left
misdescribed. Only the constant-function result, which does satisfy the stated
conditions literally, remains.

## The S₃ Trajectory Matrix Invariant

Independent numerical verification lives in
[`S3_Trajectory_Verification/`](../S3_Trajectory_Verification/) (exact-integer
Python, no floating point), cross-checked inside Lean by `ChiralSign.lean` above. For
the generator `v = (2, 1, 4)` and its full `S₃` orbit (the 6×3 matrix `M` of all
permutations of `v`'s entries):

- **Rank:** `rank(M) = 3`, unconditionally — **all 20 of the 20** possible 3×3 row
  minors are nonzero, not merely one. Any 3 of the 6 orbit rows already form a basis of
  `ℝ³`. This is a property of the whole matrix, no submatrix choice involved.
- **Determinant — stated precisely:** a determinant requires a *square* matrix, so
  "the determinant" names one specific, principled 3×3 submatrix: the images of `v`
  under `{e, (12), (23)}` — the identity and the two adjacent transpositions that
  generate `S₃` — in that order. That submatrix's determinant is exactly **−21**,
  reproved inside Lean's kernel as `canonicalOrbitMatrix_det`.
  - This is **not** a sign-independent invariant of the matrix as a whole: among all
    20 three-row minors (raw ascending-index order, no reordering), `|21|` appears 6
    times total (3× as `−21`, 3× as `+21`) — the sign flips with row-permutation
    parity, exactly as `ChiralSign.lean`'s `chiral_sign_law` predicts
    (`Matrix.det_permute`). `canonicalOrbitMatrix_swap_det = 21` and
    `canonicalOrbitMatrix_rotate_det = -21` verify this directly: an odd
    row-transposition flips `−21 → +21`; the even 3-cycle `finRotate 3` preserves it.
  - Other equally natural submatrix choices give different magnitudes entirely (e.g.
    the rotation-only submatrix `{e, (123), (132)}` gives `49`, not `21`) — see
    `S3_Trajectory_Verification/BUILD_SUMMARY.md` §3.4 for the full 20-minor
    distribution.
- **What's actually invariant:** the rank (3, unconditionally), and the *magnitude*
  `21` for the specific row-triple family generated by `{e,(12),(23)}` — its sign is a
  parity/orientation fact, not a separate free invariant.

## Path to Code

**Lean 4 modules** (in dependency/build order):
1. [`Theta0Photon/Algebra/GroundAxiom.lean`](Theta0Photon/Algebra/GroundAxiom.lean)
2. [`Theta0Photon/Algebra/FieldTower.lean`](Theta0Photon/Algebra/FieldTower.lean)
3. [`Theta0Photon/Algebra/GaloisGroup.lean`](Theta0Photon/Algebra/GaloisGroup.lean)
4. [`Theta0Photon/Geometry/ChiralSign.lean`](Theta0Photon/Geometry/ChiralSign.lean)
5. [`Theta0Photon/SetTheory/Incommensurability.lean`](Theta0Photon/SetTheory/Incommensurability.lean)
6. [`Theta0Photon/Algebra/TriadicClosure.lean`](Theta0Photon/Algebra/TriadicClosure.lean)
7. [`Theta0Photon/Algebra/UniquenessTest.lean`](Theta0Photon/Algebra/UniquenessTest.lean)
8. [`Theta0Photon/Documentation/CoreAxioms.md`](Theta0Photon/Documentation/CoreAxioms.md) (documentation, not code)
9. [`Theta0Photon/Basic.lean`](Theta0Photon/Basic.lean) / [`Theta0Photon/Statistics/CenteredKernel.lean`](Theta0Photon/Statistics/CenteredKernel.lean) — earlier, independent modules (see "What's proved" below)

**Python verification scripts:**
- [`../S3_Trajectory_Verification/verify_s3_trajectory_matrix.py`](../S3_Trajectory_Verification/verify_s3_trajectory_matrix.py)
- [`../S3_Trajectory_Verification/verification_output.txt`](../S3_Trajectory_Verification/verification_output.txt) (captured run, verbatim)
- [`../S3_Trajectory_Verification/BUILD_SUMMARY.md`](../S3_Trajectory_Verification/BUILD_SUMMARY.md)
- [`../S3_Trajectory_Verification/BUILD_SUMMARY_ChiralSign.md`](../S3_Trajectory_Verification/BUILD_SUMMARY_ChiralSign.md)

**Build history / narrative documents:**
- [`2026-09-06_Theta0Photon_Build_Summary.md`](2026-09-06_Theta0Photon_Build_Summary.md)
- [`2026-09-09_FieldTower_Ground_Axiom_Quadratic_Layer.md`](2026-09-09_FieldTower_Ground_Axiom_Quadratic_Layer.md)

---

## What's proved (earlier modules, pre-dating this milestone)

**`Theta0Photon/Basic.lean`** — a `Node`/`NodeMetric` diagonal-collapse theorem, in the
same shape as the top-level `metric_independence`:
- `zero_is_not_a_coordinate` — for any metric where `dist x x = 0`, a `P`-decorated
  relation at the diagonal collapses to the bare relation, given `P` holds at `0`.
- `off_diagonal_dist_ne_zero` / `dist_eq_zero_iff_R` — extend this to *strict* metrics
  (every off-diagonal pair has strictly positive distance): zero distance then exactly
  characterizes the relation, not just implies it on the diagonal.

**`Theta0Photon/Statistics/CenteredKernel.lean`** — a real-valued statistical analogue
built independently from the theorems above (see Scope note below):
- `finrank_centeredSubspace` — the centered subspace (kernel of the sum map on `Fin N
  → ℝ`) has dimension exactly `N - 1`.
- `sample_space_direct_sum` — the diagonal (constant-vector) subspace and the centered
  subspace are complementary (`IsCompl`).
- `diagonal_subspace_sum_sq_deviation_zero` / `diagonal_subspace_pairwise_dist_zero` —
  any sample lying in the diagonal subspace has zero variance.

Zero `sorry` across both files.

### Scope

The parallel between `Basic.lean` and `CenteredKernel.lean` is structural, not a
literal shared Lean dependency: `NodeMetric.dist` is `Nat`-valued, `Sample` is
`ℝ`-valued, and neither file's theorems appear in the other's proof term — confirmed by
inspection (`#print axioms`) rather than assumed from the shared "diagonal" language.

`Main.lean` also contains `Photon`, `Superposition`, and `EncryptedPacket` — these are
the same `Process` proof term (`zeroProcess`) under different names, i.e. a
naming/interpretation layer over `zero_is_not_a_coordinate`, not independently-proved
claims about physical photons or superposition.

## Building

From this directory:
```sh
lake exe cache get
lake build
```
CI (`.github/workflows/lean_action_ci.yml`) runs the same build on every push via
`leanprover/lean-action`.
