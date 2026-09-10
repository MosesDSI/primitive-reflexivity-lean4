# Build Summary — ChiralSign.lean (S3 Parity vs. Orientation Sign)

**Date:** 2026-09-09
**Project dir (new file lives here):** `Theta__0_Photon/Theta0Photon/Geometry/ChiralSign.lean`
**Session record (per instruction, kept in the current build folder):** `PrimitiveReflexivity/S3_Trajectory_Verification/`
**Objective:** Formalize that any odd permutation (transposition) of `Equiv.Perm (Fin 3)`
acting on a triadic coordinate matrix flips the sign of its determinant, while even
permutations preserve it — using Mathlib's real `Equiv.Perm.sign` and `Matrix.det`,
built against the pinned toolchain, zero errors, standard trust base only.
**Outcome:** Full success. 7 theorems, 0 `sorry`, `lake build Theta0Photon` and
`lake build Main` both clean (1740/1740 jobs), every theorem individually
axiom-checked to `[propext, Classical.choice, Quot.sound]` before the checks were
stripped from the shipped file.

---

## 1. File placement

`ChiralSign.lean` was placed at `Theta0Photon/Geometry/ChiralSign.lean` **inside the
actual `Theta__0_Photon` Lean project** (not inside this `S3_Trajectory_Verification`
folder) — that project already has Mathlib correctly wired via the directory junction
set up in the 2026-09-06 build, which is what "using our pinned toolchain" actually
requires. Its module namespace (`Theta0Photon.Geometry.ChiralSign`) matches the
existing sibling `Theta0Photon.Statistics.CenteredKernel`. This build's own record
(this file, and the working notes below) is kept in the current build folder,
`S3_Trajectory_Verification/`, per instruction — the two are cross-referenced rather
than duplicated.

It was wired into the library's default target (`Theta0Photon.lean` now also imports
`Theta0Photon.Geometry.ChiralSign`, alongside the existing `Basic` and
`Statistics.CenteredKernel` imports), so it is verified by the real `lake build`, not
only a standalone `lake env lean` check.

## 2. What was built

Seven theorems in `PrimitiveReflexivity.Geometry`, over a general `CommRing R` unless
noted:

1. **`chiral_sign_law`** — the general fact: permuting the rows of a `Fin 3 × Fin 3`
   matrix by `σ : Equiv.Perm (Fin 3)` scales its determinant by `sign σ`. This is
   Mathlib's own `Matrix.det_permute`, restated under the framework's vocabulary
   (row-relabelling of triadic coordinates / orientation volume form) — no new linear
   algebra, a named wrapper.
2. **`transposition_flips_orientation`** — the odd case: `σ.IsSwap → det (permuted) =
   -det`. Holds for `Equiv.Perm n` generally (via `IsSwap.sign_eq`), not only `Fin 3`.
3. **`even_permutation_preserves_orientation`** — the even case: `sign σ = 1 → det
   (permuted) = det`.
4. **`fin3_isOdd_iff_isSwap`** — the `Fin 3`-specific fact the request actually asked
   for by name ("any odd permutation (transposition)"): in `S3` specifically,
   `sign σ = -1 ↔ σ.IsSwap` — odd permutations and transpositions are exactly the same
   three group elements. Verified by exhaustive decision over all 6 elements of
   `Equiv.Perm (Fin 3)`, routed through Mathlib's `card_support_eq_two` (see §3 — the
   direct `decide` on `IsSwap` itself does not work, `IsSwap` has no registered
   `Decidable` instance). Documented in the file as **not** a general fact about
   `Equiv.Perm n` — false for `n ≥ 6` (three disjoint transpositions compose to an odd
   permutation that is not itself a single swap).
5–7. **`canonicalOrbitMatrix_det` / `_swap_det` / `_rotate_det`** — a concrete
   instantiation reusing the exact `{e, (12), (23)}` canonical submatrix of
   `v = (2, 1, 4)` from `verify_s3_trajectory_matrix.py` (§3.3 of that script's build
   summary): reproves `det = -21` inside Lean's kernel, then applies the two general
   theorems above to it directly — an odd row-swap flips it to `+21` (matching that
   same row-triple's raw-order `+21` minor already found by the Python sweep), and the
   even 3-cycle `finRotate 3` (`sign = (-1)^(3-1) = 1`, via Mathlib's `sign_finRotate`)
   leaves it at `-21`.

## 3. Problems encountered and how they were fixed

Compiled at every step against the real pinned checkout (`0df444a3`, Lean v4.33.1),
not written and assumed correct — three real errors surfaced on the first pass:

### 3.1 `decide` cannot dispatch `∀ σ, sign σ = -1 ↔ σ.IsSwap` directly
First attempt: `theorem fin3_isOdd_iff_isSwap : ∀ σ, ... ↔ σ.IsSwap := by decide`.
Failed: `failed to synthesize Decidable (∀ σ, Perm.sign σ = -1 ↔ σ.IsSwap)`.
`Equiv.Perm.IsSwap` (`∃ x y, x ≠ y ∧ f = swap x y`) has no registered `Decidable`
instance in this Mathlib revision, so the compound proposition isn't recognized as
decidable even though every piece is finite. **Fix:** rewrote via Mathlib's own
`Equiv.Perm.card_support_eq_two : #f.support = 2 ↔ IsSwap f` first, converting the
goal to `sign σ = -1 ↔ #σ.support = 2` — both sides now genuinely computable
(`ℤˣ`/`ℕ` equality) — then `revert σ; decide` closes the whole finite check over the
6 elements of `Equiv.Perm (Fin 3)`.

### 3.2 Unsolved goal left after `rw` in `canonicalOrbitMatrix_swap_det`
After `rw [h, canonicalOrbitMatrix_det]` the goal was left as the concrete arithmetic
identity `- -21 = 21`, not auto-closed by `rw` itself. **Fix:** appended `norm_num`.

### 3.3 Wrong fully-qualified name for `sign_finRotate`
First attempt referenced `Equiv.Perm.sign_finRotate`. The actual theorem, checked
directly in `Mathlib/GroupTheory/Perm/Fin.lean`, is declared under `open Equiv` (no
enclosing `namespace Equiv.Perm`), so its real fully-qualified name is the
unqualified top-level `sign_finRotate`. **Fix:** used `sign_finRotate` (already in
scope in this file via its own `open Equiv Matrix`), confirmed by successful
compilation, not by re-guessing a second qualified form.

## 4. What was verified, and how

- `lake env lean Theta0Photon/Geometry/ChiralSign.lean` — standalone compile, zero
  errors, zero warnings, after the three fixes above.
- `#print axioms` on all 7 theorems individually (run once during verification, then
  stripped from the shipped file — same discipline as `AxiomCheck.lean` in the
  original PrimitiveReflexivity build): every one reports exactly
  `[propext, Classical.choice, Quot.sound]`, Lean/Mathlib's standard trust base.
  No `sorryAx`, no project-defined axioms, on any theorem.
- `lake build Theta0Photon` (the real default target, after wiring the new import
  into `Theta0Photon.lean`) — **1740/1740 jobs, clean.**
- `lake build Main` — re-run after the root-file edit to confirm no regression to the
  existing `Main.lean` / `Basic.lean` / `CenteredKernel.lean` chain — **1740/1740
  jobs, clean.**

## 5. Explicitly not claimed

Per the request's framing ("formalize the structural link between our verified Lean 4
ground axiom and the chiral sign-flipping behavior"), this is addressed directly in
`ChiralSign.lean`'s own module doc rather than left implicit: **there is no formal
derivation connecting `triadic_ground_irreducible` (the `X² - n` irreducibility
theorem) to anything in this file.** They are theorems in unrelated domains — one is
number-theoretic irreducibility over `ℚ[X]`, the other is a representation/
multilinear-algebra fact about `S3` acting on `Matrix (Fin 3) (Fin 3) R` — and neither
file imports or references the other's declarations. The shared subject matter (the
triadic `(n, √n, n²)` construction and its `S3` orbit) is a real thematic link; a
formal one was not manufactured to force the appearance of a dependency that doesn't
exist in the actual proof terms.

## 6. Files

- `Theta__0_Photon/Theta0Photon/Geometry/ChiralSign.lean` — the deliverable (new).
- `Theta__0_Photon/Theta0Photon.lean` — updated, one new import line added.
- `PrimitiveReflexivity/S3_Trajectory_Verification/BUILD_SUMMARY_ChiralSign.md` — this
  file.

## 7. Open items

- `fin3_isOdd_iff_isSwap` is specific to `Fin 3`; if this framework later needs the
  analogous fact for a larger `Equiv.Perm n`, it is **not** a `sign = -1 ↔ IsSwap`
  statement — a genuinely different characterization (e.g. via `cycleType`) would be
  needed, and is out of scope here.
- `canonicalOrbitMatrix_swap_det` and `_rotate_det` each check the chiral-sign law
  against exactly one row-transposition and one row-rotation of one concrete matrix;
  they are illustrative instances of the two general theorems, not an exhaustive
  re-verification of all 20 minors from the Python sweep inside Lean (that sweep
  already stands on its own in `verify_s3_trajectory_matrix.py`).
