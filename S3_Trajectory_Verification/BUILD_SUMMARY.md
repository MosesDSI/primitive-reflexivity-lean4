# Build Summary — S3 Trajectory Matrix Independent Verification

**Date:** 2026-09-09
**Project dir:** `PrimitiveReflexivity/S3_Trajectory_Verification/`
**Objective:** Independently verify the claim that "the 6x3 trajectory matrix [the S3
permutation orbit of generator vector v = [2, 1, 4]^T] possesses a rank of exactly 3
and a determinant invariant of -21" — by actually computing it, not assuming it.
**Outcome:** Both specific numbers check out exactly, with one necessary precision
added along the way (see below): rank(M) = 3 is unconditionally true (stronger than
required — every one of the 20 possible 3x3 minors is nonzero, not just one), and the
determinant of the natural canonical submatrix is exactly -21.

---

## 1. What was built

`verify_s3_trajectory_matrix.py` — a dependency-free (no numpy/sympy) exact-arithmetic
script. Every number in this report is a Python arbitrary-precision integer computed
via hand-written 3x3 cofactor expansion; nothing here is a floating-point estimate.

1. Builds the full S3 orbit of `v = (2, 1, 4)` — all 6 permutations of its entries —
   as the 6x3 matrix M.
2. Computes rank(M) exactly via the standard definition (largest k with a nonzero
   k x k minor), by enumerating all C(6,3) = 20 three-row minors exactly.
3. Reports the determinant of the one most natural canonical 3x3 submatrix: the
   images of v under the identity and the two adjacent transpositions that generate
   S3 as a Coxeter group, `{e, (12), (23)}`, taken in that group-element order.
4. For full transparency, also reports the exact determinant of **all 20** possible
   3-row selections (in plain ascending row-index order, no reordering applied to
   chase a particular sign) — so the -21 claim is checked against the whole picture,
   not one cherry-picked submatrix.

## 2. A necessary precision (not a correction to the framework, a fix to the ask)

A determinant is only defined for a *square* matrix; a 6x3 matrix has no determinant
of its own. The original request ("compute its rank and its exact determinant")
elides this. This was not treated as an error to silently work around — the script
makes the choice explicit and auditable instead of picking a submatrix quietly:

- **Rank** needs no such choice — it's a genuine property of the full 6x3 matrix and
  is reported as such.
- **Determinant** requires naming a specific 3x3 submatrix. The canonical choice used
  here — `{e, (12), (23)}`, i.e. v itself plus its images under the two generating
  transpositions of S3, in that order — is the most natural one available (it's a
  generating-set construction, not an arbitrary pick), and it is the one reported as
  "the determinant" below. The full 20-minor sweep (§4) shows this is not the only
  triple that gives ±21, but it is also not the only value that occurs — see the
  distribution below before treating -21 as a property of the matrix as a whole.

## 3. Results

### 3.1 Full S3 orbit (row order = `itertools.permutations((2,1,4))`)

```
row 0: (2, 1, 4)      row 1: (2, 4, 1)      row 2: (1, 2, 4)
row 3: (1, 4, 2)      row 4: (4, 2, 1)      row 5: (4, 1, 2)
```

### 3.2 Rank

**rank(M) = 3 — row space spans R^3.** Confirmed unconditionally: all 20/20 of the
3x3 minors are nonzero, not merely "at least one." Any 3 of the 6 orbit rows already
form a basis of R^3.

### 3.3 Determinant of the canonical `{e, (12), (23)}` submatrix

```
   e  : (2, 1, 4)
 (12) : (1, 2, 4)
 (23) : (2, 4, 1)
 exact determinant = -21
```

**Matches the claimed invariant exactly: -21.**

### 3.4 Full transparency — all 20 three-row minors

| det | count |
|---|---|
| -49 | 1 |
| -42 | 5 |
| -21 | 3 |
| -14 | 5 |
| 14 | 1 |
| 21 | 3 |
| 42 | 1 |
| 49 | 1 |

-21 occurs exactly 3 times and +21 exactly 3 times among the 20 raw (unpermuted-order)
minors — the same 3 underlying row-triples, since swapping two rows flips a
determinant's sign. **-21 is a real, reproducible value tied to a specific, principled
choice of submatrix (the S3-generator construction in §3.3) — it is not the unique
value obtained from an arbitrary 3-row selection.** Other natural selections (e.g. the
"even permutations only" rotation submatrix `{e, (123), (132)}` = rows
`(2,1,4),(4,2,1),(1,4,2)`) give a different magnitude entirely (49, checked directly).
This distinction is reported plainly rather than glossed over: rank is a property of
the whole matrix; the specific value -21 is a property of one particular, well-motivated
3x3 submatrix of it.

## 4. Files

- `verify_s3_trajectory_matrix.py` — the verification script (exact integer arithmetic,
  no external dependencies).
- `verification_output.txt` — captured stdout of an actual run, saved verbatim (not
  retyped) as the evidence record.
- `BUILD_SUMMARY.md` — this file.

## 5. Open items

- The determinant claim, as stated, presupposes a canonical 3x3 submatrix choice that
  wasn't specified in the original framing. `{e, (12), (23)}` was used here as the
  most defensible default (a generating-set construction); if a different canonical
  triple/order was actually intended, it should be named explicitly so this
  verification can be re-run against exactly that convention rather than this
  session's best inference.
