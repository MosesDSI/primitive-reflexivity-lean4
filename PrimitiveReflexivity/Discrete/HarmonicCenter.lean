import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimitiveReflexivity.Discrete

/-!
# Discrete Harmonic Centers and Symmetric Partitions
The discrete interval `omega k = {1, ..., 2k+1}` has a harmonic center at
`k + 1`: distances to that center are symmetric about it, and a mod-3
partition of `{1, ..., 21}` (the `k = 10` case) has its middle class `C2`
containing the center and achieving the minimal total distance sum.
-/

/-- The discrete interval `{1, ..., 2k+1}`. -/
def omega (k : ℕ) : Finset ℤ := Finset.Icc 1 (2 * (k : ℤ) + 1)

/-- The distance from any point `k+1+j` to the center `k+1` equals the
distance from its mirror point `k+1-j` to the same center. -/
theorem harmonic_distance_symmetry (k : ℕ) (j : ℤ) :
    |((k : ℤ) + 1 - j) - ((k : ℤ) + 1)| = |((k : ℤ) + 1 + j) - ((k : ℤ) + 1)| := by
  have h1 : ((k : ℤ) + 1 - j) - ((k : ℤ) + 1) = -j := by ring
  have h2 : ((k : ℤ) + 1 + j) - ((k : ℤ) + 1) = j := by ring
  rw [h1, h2, abs_neg]

/-- The three residue classes of `{1, ..., 21}` mod 3. -/
def C1 : Finset ℤ := (Finset.Icc (1 : ℤ) 21).filter (fun n => n % 3 = 1)
def C2 : Finset ℤ := (Finset.Icc (1 : ℤ) 21).filter (fun n => n % 3 = 2)
def C3 : Finset ℤ := (Finset.Icc (1 : ℤ) 21).filter (fun n => n % 3 = 0)

/-- The harmonic center of `{1, ..., 21}` (`k = 10`, center `k+1 = 11`) lies
in the middle residue class `C2`. -/
theorem harmonic_center_in_C2 : (11 : ℤ) ∈ C2 := by decide

/-- Total distance from a point `p` to every element of a finite set `s`. -/
def distSum (p : ℤ) (s : Finset ℤ) : ℤ := ∑ c ∈ s, |c - p|

/-- The middle class `C2` (containing the harmonic center) has the strictly
smallest total distance sum from the center among the three classes. -/
theorem tri_partition_distance_sums :
    distSum 11 C1 = 37 ∧ distSum 11 C2 = 36 ∧ distSum 11 C3 = 37 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end PrimitiveReflexivity.Discrete
