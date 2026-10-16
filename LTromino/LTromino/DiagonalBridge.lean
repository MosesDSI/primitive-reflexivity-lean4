import LTromino.Base

/-!
# LTromino.DiagonalBridge — the cell diagonals and the diagonal statistic agree

`Statistics/CenteredKernel.lean` (Mathlib, ℝ) splits a two-cell sample into a
diagonal (constant) part along `D1 = (1, 1)` and a centered (zero-sum) part
along `D2 = (1, −1)`. `Base.lean` (core, Bool) splits the four cells of the
2×2 into the main diagonal `onD1` and the anti-diagonal.

This file checks, cell by cell and with no axioms, that the two splits are the
same split, read on the cells themselves rather than on real samples:

* the shared coordinate `x + y` and the depth coordinate `x − y` of a cell are
  its pairings with `D1` and `D2`;
* once the cell is read from the phantom middle (bits as `±1`, Base `cen`),
  the D1 cells are exactly the constant samples and the D2 cells are exactly
  the zero-sum samples;
* read from a corner instead (bits as `0/1`), the D2 cells are not zero-sum,
  so the identification needs the phantom middle as origin.

Everything is a finite statement over bits, decided by the kernel. Values are
integers; no division, no ℝ.
-/

namespace LTromino

/-- `CenteredKernel.D1`, with entries as integers: the all-ones direction. -/
def vD1 : Int × Int := (1, 1)
/-- `CenteredKernel.D2`, with entries as integers: index 0 ↦ 1, index 1 ↦ −1. -/
def vD2 : Int × Int := (1, -1)

/-- Pairing of two integer pairs. -/
def pair (u v : Int × Int) : Int := u.1 * v.1 + u.2 * v.2

/-- A cell read from the corner: bits as 0/1. -/
def raw (c : Cell) : Int × Int := (bitI c.1, bitI c.2)
/-- A cell read from the phantom middle: bits as ±1. -/
def mid (c : Cell) : Int × Int := (cen c.1, cen c.2)

/-! ## The two diagonal directions -/

/-- `square_diagonals_orthogonal`, on integers. -/
theorem vD1_vD2_orthogonal : pair vD1 vD2 = 0 := by decide

/-- The anti-diagonal direction is zero-sum (`d2_in_centered_subspace`). -/
theorem vD2_centered : vD2.1 + vD2.2 = 0 := by decide

/-! ## The §15b coordinates are the pairings with D1 and D2 -/

/-- The shared coordinate of a cell is its pairing with `D1`, and the depth
    coordinate is its pairing with `D2`: Boundary §15b, Base §5 and
    CenteredKernel use one pair of directions. -/
theorem cell_coords_are_pairings : ∀ x y : Bool,
    cellD1 (x, y) = pair (raw (x, y)) vD1 ∧ cellD2 (x, y) = pair (raw (x, y)) vD2 := by
  decide

/-- **No halving.** Twice each coordinate is the shared part plus or minus the
    depth part. This is `sample_decomp_two` with both sides multiplied by 2,
    which keeps it on the integers. -/
theorem decomp_no_halving : ∀ x y : Bool,
    2 * bitI x = cellD1 (x, y) + cellD2 (x, y) ∧ 2 * bitI y = cellD1 (x, y) - cellD2 (x, y) := by
  decide

/-! ## The cell diagonals are the diagonal and centered subspaces -/

/-- **D1 cells are the constant samples.** From the phantom middle, a cell lies
    on the main diagonal exactly when its two coordinates agree, i.e. it lies
    in `DiagonalSubspace 2`. -/
theorem onD1_iff_constant : ∀ x y : Bool, onD1 (x, y) = true ↔ (mid (x, y)).1 = (mid (x, y)).2 := by
  decide

/-- **D2 cells are the zero-sum samples.** From the phantom middle, a cell lies
    on the anti-diagonal exactly when its coordinates sum to zero, i.e. it lies
    in `CenteredSubspace 2`. -/
theorem onD2_iff_centered : ∀ x y : Bool,
    onD1 (x, y) = false ↔ (mid (x, y)).1 + (mid (x, y)).2 = 0 := by
  decide

/-- Every cell is one or the other, never both (`sample_space_direct_sum`, on
    the four cells): the only sample that is both constant and zero-sum is 0,
    and 0 is not a cell. The origin sits at the phantom middle, which is not
    a node. -/
theorem cell_in_exactly_one : ∀ x y : Bool,
    (decide ((mid (x, y)).1 = (mid (x, y)).2) != decide ((mid (x, y)).1 + (mid (x, y)).2 = 0)) = true := by
  decide

/-- **Zero dispersion on D1** (`diagonal_subspace_sum_sq_deviation_zero`):
    the depth coordinate vanishes exactly on the main diagonal. -/
theorem depth_zero_iff_onD1 : ∀ x y : Bool, pair (mid (x, y)) vD2 = 0 ↔ onD1 (x, y) = true := by
  decide

/-- Dually, the shared (mean) coordinate vanishes exactly on the anti-diagonal. -/
theorem mean_zero_iff_onD2 : ∀ x y : Bool, pair (mid (x, y)) vD1 = 0 ↔ onD1 (x, y) = false := by
  decide

/-! ## Necessity: the origin must be the phantom middle -/

/-- **Read from a corner, the split fails.** The cell (0, 1) is on the
    anti-diagonal, but its 0/1 coordinates sum to 1, not 0, so it is not a
    centered sample. -/
theorem raw_origin_breaks_centering :
    onD1 (false, true) = false ∧ (raw (false, true)).1 + (raw (false, true)).2 = 1 := by
  decide

/-- Read from a corner, the D1 cell (0,0) is both constant and zero-sum, so the
    two parts overlap and the split is no longer exclusive. -/
theorem raw_origin_breaks_exclusivity :
    onD1 (false, false) = true ∧ (raw (false, false)).1 = (raw (false, false)).2 ∧
      (raw (false, false)).1 + (raw (false, false)).2 = 0 := by
  decide

/-! ## The chiral swap acts on the statistic as it does on the cells -/

/-- The swap fixes the mean coordinate and negates the depth coordinate,
    on the centred reading as well (cf. `chiral_swap_on_cells`). -/
theorem chiral_swap_on_statistic : ∀ x y : Bool,
    pair (mid (act reflD1 (x, y))) vD1 = pair (mid (x, y)) vD1 ∧
    pair (mid (act reflD1 (x, y))) vD2 = -pair (mid (x, y)) vD2 := by
  decide

/-- The Phantom Middle π negates the whole centred sample: both coordinates
    flip sign together, so π fixes which subspace a cell lies in. -/
theorem phantom_middle_negates_sample : ∀ x y : Bool,
    mid (act rot180 (x, y)) = (-(mid (x, y)).1, -(mid (x, y)).2) := by
  decide

end LTromino

