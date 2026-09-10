import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
# Chiral Sign: S3 Parity and the Orientation of Triadic Coordinates

This file formalizes the parity/orientation fact underlying the S3 permutation
orbit used elsewhere in this framework (see
`S3_Trajectory_Verification/` for the numerical companion): relabelling the
three rows of a triadic coordinate matrix by a permutation `σ : Equiv.Perm
(Fin 3)` scales its determinant — the orientation volume form — by
`Equiv.Perm.sign σ`. An odd permutation (a transposition, in `Fin 3`
specifically the *only* odd elements — see `fin3_isOdd_iff_isSwap` below)
flips the sign; an even permutation preserves it.

**Scope note, stated once and not repeated as a running hedge:** the core fact
here (`chiral_sign_law`) is exactly Mathlib's own `Matrix.det_permute`,
restated under the framework's vocabulary — no new linear algebra is
introduced. This file does **not** formally derive anything from
`triadic_ground_irreducible` (the `X^2 - n` irreducibility ground axiom
verified separately). The two theorems live in genuinely different domains —
one is a number-theoretic irreducibility statement over `ℚ[X]`, the other is a
representation/multilinear-algebra fact about `S3` acting on `Matrix (Fin 3)
(Fin 3) R` — and no Lean import or term in either file references the other.
The link between them is the shared subject matter (the triadic `(n, √n, n^2)`
construction and its `S3` orbit), not a formal dependency; manufacturing an
artificial import to force one would misrepresent what is actually proved.
-/

namespace PrimitiveReflexivity.Geometry

open Equiv Matrix

variable {R : Type*} [CommRing R]

/-- **Chiral sign law.** Relabelling the rows of a `Fin 3 × Fin 3` matrix by a
permutation `σ` scales its determinant by `sign σ`. This is Mathlib's
`Matrix.det_permute` verbatim, named for the geometric reading used in this
framework: the determinant is the orientation volume form of the three
triadic coordinate rows, and `σ` acts on which row sits in which position. -/
theorem chiral_sign_law (M : Matrix (Fin 3) (Fin 3) R) (σ : Equiv.Perm (Fin 3)) :
    (M.submatrix σ id).det = Equiv.Perm.sign σ * M.det :=
  Matrix.det_permute σ M

/-- **Odd case.** Any transposition of the three rows negates the orientation:
swapping exactly two of the three triadic coordinate rows flips the sign of
the determinant. `Equiv.Perm.IsSwap` is the standard Mathlib formalization of
"is a transposition" (`∃ x y, x ≠ y ∧ σ = Equiv.swap x y`), and this holds for
`Equiv.Perm n` over any `n`, not only `Fin 3`. -/
theorem transposition_flips_orientation (M : Matrix (Fin 3) (Fin 3) R)
    {σ : Equiv.Perm (Fin 3)} (hσ : σ.IsSwap) :
    (M.submatrix σ id).det = -M.det := by
  rw [chiral_sign_law, hσ.sign_eq]
  simp

/-- **Even case.** Any even permutation of the three rows preserves the
orientation. -/
theorem even_permutation_preserves_orientation (M : Matrix (Fin 3) (Fin 3) R)
    {σ : Equiv.Perm (Fin 3)} (hσ : Equiv.Perm.sign σ = 1) :
    (M.submatrix σ id).det = M.det := by
  rw [chiral_sign_law, hσ]
  simp

/-- **`Fin 3`-specific fact.** In `Equiv.Perm (Fin 3)` (the symmetric group S3
acting on the triadic coordinates), "odd permutation" and "transposition" are
literally the same three elements: `sign σ = -1 ↔ σ.IsSwap`. This is *not*
true of `Equiv.Perm n` in general for `n ≥ 6` (a product of three disjoint
transpositions is odd but is not itself a single transposition) — it is a
genuine fact about `S3` specifically, checked here by exhaustive decision over
its 6 elements rather than assumed from the general theory. -/
theorem fin3_isOdd_iff_isSwap :
    ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = -1 ↔ σ.IsSwap := by
  intro σ
  rw [← Equiv.Perm.card_support_eq_two]
  revert σ
  decide

/-!
## A concrete instance: the canonical S3-orbit matrix of `v = (2, 1, 4)`

The rows below are exactly the `{e, (12), (23)}` canonical submatrix from the
independent numerical verification in
`S3_Trajectory_Verification/verify_s3_trajectory_matrix.py`: row 0 is the
generator `v = (2, 1, 4)` itself (the identity), row 1 is `v` under the
transposition swapping coordinates 0 and 1, row 2 is `v` under the
transposition swapping coordinates 1 and 2. That script measured its
determinant as exactly `-21` over the integers by direct cofactor expansion;
the theorem below reproves the same number inside Lean's kernel, and the two
that follow verify the chiral-sign law against it concretely: an odd
row-permutation flips `-21` to `+21`, and the even 3-cycle `finRotate 3`
(`sign = (-1)^(3-1) = 1`, via Mathlib's `sign_finRotate`) leaves it at `-21`.
-/

/-- The canonical `{e, (12), (23)}` orbit submatrix of `v = (2, 1, 4)`. -/
def canonicalOrbitMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 1, 4; 1, 2, 4; 2, 4, 1]

theorem canonicalOrbitMatrix_det : canonicalOrbitMatrix.det = -21 := by
  simp [canonicalOrbitMatrix, Matrix.det_fin_three]

/-- Swapping rows 1 and 2 (the `(12)v` and `(23)v` rows) is a transposition,
hence odd: the orientation flips from `-21` to `+21`, matching the raw-order
`+21` minor already found by the Python sweep for this same row triple. -/
theorem canonicalOrbitMatrix_swap_det :
    (canonicalOrbitMatrix.submatrix (Equiv.swap (1 : Fin 3) 2) id).det = 21 := by
  have hswap : (Equiv.swap (1 : Fin 3) 2).IsSwap := ⟨1, 2, by decide, rfl⟩
  have h := transposition_flips_orientation canonicalOrbitMatrix hswap
  rw [h, canonicalOrbitMatrix_det]
  norm_num

/-- The 3-cycle `finRotate 3` is even (`sign = (-1)^(3-1) = 1`), so cyclically
rotating all three rows preserves the orientation exactly, still `-21`. -/
theorem canonicalOrbitMatrix_rotate_det :
    (canonicalOrbitMatrix.submatrix (finRotate 3) id).det = -21 := by
  have heven : Equiv.Perm.sign (finRotate 3) = 1 := by
    rw [sign_finRotate]; decide
  have h := even_permutation_preserves_orientation canonicalOrbitMatrix heven
  rw [h, canonicalOrbitMatrix_det]

end PrimitiveReflexivity.Geometry
