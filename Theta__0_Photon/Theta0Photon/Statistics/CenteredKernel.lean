import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Centered Kernel and the N - 1 Degrees of Freedom

The centered subspace of finite real samples is the kernel of the summation
map. The diagonal identity from the R3 model is represented here by the
constant-vector direction, while centered deviations satisfy one linear
constraint.
-/

namespace PrimitiveReflexivity.Statistics

variable {N : ℕ} [NeZero N]

/-- A sample of size `N` mapped to the real continuum. Reducible: it must be
transparent to typeclass search so that `Fin N → ℝ`'s `Module ℝ` structure
(needed once we destructure a `DiagonalSubspace` membership proof into an
explicit scalar multiple) is visible on `Sample N` as well. -/
abbrev Sample (N : ℕ) := Fin N → ℝ

/-- The arithmetic mean of a sample of size `N`. -/
noncomputable def sampleMean (s : Sample N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, s i

/-- The centered deviation of the `i`th observation from the sample mean. -/
noncomputable def deviation (s : Sample N) (i : Fin N) : ℝ :=
  s i - sampleMean s

/-- Centered deviations sum to zero. -/
theorem deviations_sum_zero (s : Sample N) :
    ∑ i : Fin N, deviation s i = 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp only [deviation]
  rw [Finset.sum_sub_distrib (f := s) (g := fun _ => sampleMean s), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [sampleMean]
  rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul, sub_self]

/-- The linear summation map over finite real samples. -/
def sumMap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- The centered subspace, namely the kernel of `sumMap`. -/
def CenteredSubspace (N : ℕ) : Submodule ℝ (Fin N → ℝ) :=
  LinearMap.ker (sumMap N)

/-- The constant-vector, or diagonal, subspace. -/
def DiagonalSubspace (N : ℕ) : Submodule ℝ (Fin N → ℝ) :=
  Submodule.span ℝ {v : Fin N → ℝ | ∃ c : ℝ, v = fun _ => c}

/-- Main diagonal of the two-cell coordinate model. -/
def D1 : Fin 2 → ℝ := fun _ => 1

/-- Anti-diagonal of the two-cell coordinate model. -/
def D2 : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1

/-- The two diagonals of the unit square are orthogonal. -/
theorem square_diagonals_orthogonal :
    ∑ i : Fin 2, D1 i * D2 i = 0 := by
  norm_num [D1, D2, Fin.sum_univ_two]

/-- The anti-diagonal lies in the centered subspace. -/
theorem d2_in_centered_subspace : D2 ∈ CenteredSubspace 2 := by
  change ∑ i : Fin 2, D2 i = 0
  norm_num [D2, Fin.sum_univ_two]

/-- Every two-cell sample decomposes into its diagonal mean and centered part. -/
theorem sample_decomp_two (s : Sample 2) :
    s = (fun i => sampleMean s * D1 i) + (fun i => deviation s i) := by
  funext i
  simp only [Pi.add_apply, D1, deviation]
  ring

/-- The two-cell sample space splits into the diagonal and centered directions. -/
theorem two_cell_direct_sum :
    ∀ s : Sample 2, ∃ a : ℝ, ∃ v : CenteredSubspace 2,
      s = (fun _ => a) + (v : Fin 2 → ℝ) := by
  intro s
  refine ⟨sampleMean s, ⟨fun i => deviation s i, deviations_sum_zero s⟩, ?_⟩
  have h := sample_decomp_two s
  simp only [D1, mul_one] at h
  exact h

/-!
### General N: projecting onto the mean costs exactly one degree of freedom
-/

/-- `sumMap N` does not vanish identically, since it sends the all-ones
sample to `N ≠ 0`. -/
theorem sumMap_ne_zero : sumMap N ≠ 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hval : sumMap N (fun _ => (1 : ℝ)) = (N : ℝ) := by
    simp [sumMap]
  intro h
  apply hN
  have h0 : sumMap N (fun _ => (1 : ℝ)) = 0 := by rw [h]; simp
  rwa [hval] at h0

/-- Rank-nullity for the summation functional: the centered subspace (its
kernel) has dimension exactly `N - 1`, expressed additively (`finrank + 1 = N`)
to avoid truncated `ℕ` subtraction. Projecting onto the 1-dimensional
mean/diagonal direction consumes exactly one degree of freedom out of `N`. -/
theorem finrank_centeredSubspace :
    Module.finrank ℝ (CenteredSubspace N) + 1 = N := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero sumMap_ne_zero (V₁ := Fin N → ℝ)
  rwa [Module.finrank_fin_fun] at h

/-!
### The diagonal and centered subspaces are complementary
-/

omit [NeZero N] in
/-- `DiagonalSubspace N` is exactly the span of the all-ones vector: it is
already closed under addition and scalar multiplication, so taking its span
adds nothing beyond that single generator. -/
theorem diagonalSubspace_eq_span :
    DiagonalSubspace N = Submodule.span ℝ {(fun _ : Fin N => (1 : ℝ))} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, by funext i; simp⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨1, rfl⟩

/-- The all-ones diagonal direction and the centered (zero-sum) subspace
together span the whole sample space with no overlap: projecting onto the
mean (the diagonal) and subtracting it off (landing in the centered
subspace) is a genuine direct-sum decomposition, not merely two subspaces
sitting near each other. -/
theorem sample_space_direct_sum (N : ℕ) [NeZero N] :
    IsCompl (DiagonalSubspace N) (CenteredSubspace N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hu_ne : (fun _ : Fin N => (1 : ℝ)) ≠ 0 := by
    intro h
    have h0 := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
    norm_num at h0
  have hp : DiagonalSubspace N ≠ ⊥ := by
    rw [diagonalSubspace_eq_span, Ne, Submodule.span_singleton_eq_bot]
    exact hu_ne
  have hdisj : Disjoint (CenteredSubspace N) (DiagonalSubspace N) := by
    rw [Submodule.disjoint_def]
    intro v hv hvd
    rw [diagonalSubspace_eq_span, Submodule.mem_span_singleton] at hvd
    obtain ⟨a, rfl⟩ := hvd
    have hker : sumMap N (a • fun _ : Fin N => (1 : ℝ)) = 0 := hv
    have ha0 : a * (N : ℝ) = 0 := by
      simpa [sumMap, mul_comm] using hker
    have ha : a = 0 := (mul_eq_zero.mp ha0).resolve_right hN
    simp [ha]
  exact (Module.Dual.isCompl_ker_of_disjoint_of_ne_bot sumMap_ne_zero hdisj hp).symm

/-!
### The diagonal subspace carries no dispersion

These are the real-valued statistical analogue of `zero_is_not_a_coordinate`
in `Main.lean`: there, an external `P`-decoration collapses to the bare
relation at the diagonal because the metric's diagonal law forces
`dist x x = 0`. Here, a sample sitting in `DiagonalSubspace N` is forced to
be a single repeated value (by `diagonalSubspace_eq_span`), so every notion
of spread built from it collapses to zero. The parallel is structural, not a
literal shared Lean dependency: `NodeMetric.dist` is `Nat`-valued while
`Sample` is `ℝ`-valued, so nothing here is derived from `Main.lean`'s
declarations; each theorem below is proved directly from
`diagonalSubspace_eq_span`.
-/

omit [NeZero N] in
/-- Every pair of coordinates of a diagonal sample agree: the diagonal
carries no coordinate-to-coordinate variation. -/
theorem diagonal_subspace_pairwise_dist_zero (s : Sample N) (hs : s ∈ DiagonalSubspace N)
    (i j : Fin N) : s i - s j = 0 := by
  rw [diagonalSubspace_eq_span] at hs
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
  simp

/-- A diagonal sample's every coordinate already equals the sample mean, so
its centered deviation is identically zero. -/
theorem diagonal_subspace_deviation_zero (s : Sample N) (hs : s ∈ DiagonalSubspace N)
    (i : Fin N) : deviation s i = 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [diagonalSubspace_eq_span] at hs
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
  simp only [deviation, sampleMean, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hN, one_mul, sub_self]

/-- The diagonal subspace has zero variance: the sum of squared deviations
from the mean vanishes identically for any sample lying on the diagonal. -/
theorem diagonal_subspace_sum_sq_deviation_zero (s : Sample N) (hs : s ∈ DiagonalSubspace N) :
    ∑ i : Fin N, deviation s i ^ 2 = 0 := by
  simp [diagonal_subspace_deviation_zero s hs]

end PrimitiveReflexivity.Statistics
