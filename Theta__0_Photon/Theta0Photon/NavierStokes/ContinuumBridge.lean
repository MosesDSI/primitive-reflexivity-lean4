import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Theta0Photon.SetTheory.Incommensurability

/-!
# Continuum Bridge: Discrete Lattice Energy Barrier and Structure-Preservation Emptiness

Two independent theorems connecting this project's discrete/continuum orthogonality
result (`isEmpty_structurePreserving_of_operationallyOrthogonal`, in
`Incommensurability.lean`) to a discrete-lattice Lipschitz bound and to the specific
carrier space `EuclideanSpace ℝ (Fin 3)` used by the OpenAI Navier-Stokes repository
audited in `CONTINUUM_ASSUMPTION_COMPARATIVE_AUDIT.md`.

**Two corrections made against the originally supplied draft, both caught by direct
compilation in this session, not by reading:**
1. The draft's closing step used `div_le_div`, which does not exist under that name
   in this project's pinned Mathlib revision (`unknown identifier`, confirmed by a
   failing standalone compile) — replaced with `gcongr`, which discharges the same
   monotonicity goal without depending on a specific lemma name.
2. The draft's `continuous_fluid_embedding_empty` stated `Monotone f` for a bare
   `[Countable DiscreteLattice]` with no order structure — `Monotone` requires a
   `Preorder` instance that hypothesis does not supply, and the draft failed to
   compile with `failed to synthesize instance Preorder DiscreteLattice` (confirmed,
   not assumed). Fixed by restating with the file's own general `PreservesStructure`
   predicate parameter, exactly matching how `isEmpty_structurePreserving_of_operationallyOrthogonal`
   is already designed to be used generically in `Incommensurability.lean`.

**What this file does not claim:** neither theorem here asserts anything about
OpenAI's Navier-Stokes proof itself, bounds its blow-up construction, or resolves
any part of it. `discrete_lattice_prevents_gradient_blowup` is a freestanding fact
about discrete metric spaces with a minimum node spacing and a pointwise-bounded
function; `continuous_fluid_embedding_empty` is a direct instance of this project's
own existing orthogonality theorem at the concrete carrier space
`EuclideanSpace ℝ (Fin 3)`. See `CONTINUUM_ASSUMPTION_COMPARATIVE_AUDIT.md` §5.2 for
why this document does not treat either as bearing on the continuum PDE result.

**Finite sub-harmonic cutoff and its bridge to the gradient bound:** `ValidLevel`,
`validLevel_finite`, `h_seq`, `IsMaxValidLevel`, and the two `gradient_bound_*`
theorems below add a second, independent pair of scales that must not be
conflated with each other:
- `h_seq L₀ N_max` is the **dynamic sub-harmonic lattice spacing** — the
  terminating physical scale reached after `N_max` geometric halvings of the
  base length `L₀`, where `N_max` is itself finite and explicitly computable
  (`exists_isMaxValidLevel`, via `Finset.max'` on the finite set
  `validLevel_finite` produces): it is *derived* from the refinement process
  and shrinks with every level.
- `h_min` is the **extrinsic material yield floor** — an atomic- or
  Nyquist–Brillouin-type cutoff, fixed independently of the refinement
  process, below which the discrete difference quotient in
  `discrete_lattice_prevents_gradient_blowup` no longer corresponds to
  anything a continuum limit could mean. It is an *external* threshold the
  process is checked against, not a quantity the process produces.

`gradient_bound_at_max_valid_level` instantiates the gradient bound at the
terminating scale `h_seq L₀ N_max`; `gradient_bound_le_of_max_valid_level` is
the bridge inequality between the two scales above, showing that bound is in
particular no worse than `2√E_total / h_min` stated purely in terms of the
fixed floor — because `h_min ≤ h_seq L₀ N_max` holds by construction of
`N_max` (`IsMaxValidLevel`'s first component).
-/

namespace Theta0Photon.NavierStokesBridge

/-- On a discrete metric space where every pair of distinct points is separated by
at least `h_min > 0`, a function pointwise-bounded by `√E_total` has its discrete
difference quotient uniformly bounded by `2√E_total / h_min`. This is a direct
Lipschitz-type consequence of the two hypotheses together — not a claim about any
specific PDE, and not itself a statement that "prevents gradient blowup" in any
continuum sense; it bounds a discrete difference quotient on a lattice with a
positive minimum spacing, which is a different mathematical object from a continuum
derivative. -/
theorem discrete_lattice_prevents_gradient_blowup
    (NodeSpace : Type*) [MetricSpace NodeSpace]
    (h_min : ℝ) (h_pos : 0 < h_min)
    (h_discrete : ∀ x y : NodeSpace, x ≠ y → h_min ≤ dist x y)
    (u : NodeSpace → ℝ) (E_total : ℝ) (_hE : 0 ≤ E_total)
    (h_energy : ∀ x : NodeSpace, (u x) ^ 2 ≤ E_total) :
    ∀ x y : NodeSpace, x ≠ y →
      |u x - u y| / dist x y ≤ (2 * Real.sqrt E_total) / h_min := by
  intro x y hne
  have hdist : h_min ≤ dist x y := h_discrete x y hne
  have hdist_pos : 0 < dist x y := lt_of_lt_of_le h_pos hdist
  have hu_diff : |u x - u y| ≤ 2 * Real.sqrt E_total := by
    have hux : |u x| ≤ Real.sqrt E_total := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (h_energy x)
    have huy : |u y| ≤ Real.sqrt E_total := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (h_energy y)
    calc |u x - u y|
      _ ≤ |u x| + |u y| := abs_sub (u x) (u y)
      _ ≤ Real.sqrt E_total + Real.sqrt E_total := add_le_add hux huy
      _ = 2 * Real.sqrt E_total := by ring
  have hsqrt_nonneg : 0 ≤ Real.sqrt E_total := Real.sqrt_nonneg E_total
  gcongr

/-- `EuclideanSpace ℝ (Fin 3)` is uncountable — proved by exhibiting an explicit
injection from `ℝ` along one coordinate, since no automatic Mathlib instance
resolves this directly for the `PiLp`-based `EuclideanSpace` type (confirmed: a
bare `infer_instance` attempt fails with `synthInstanceFailed` in this project's
pinned Mathlib revision). -/
theorem uncountable_euclideanSpace3 : Uncountable (EuclideanSpace ℝ (Fin 3)) := by
  have hinj : Function.Injective
      (fun r : ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm ![r, 0, 0]) := by
    intro a b hab
    simpa using congrFun (congrArg (EuclideanSpace.equiv (Fin 3) ℝ) hab) 0
  exact hinj.uncountable

/-- A direct instance of `isEmpty_structurePreserving_of_operationallyOrthogonal`
at the concrete carrier space `EuclideanSpace ℝ (Fin 3)`: for any countable discrete
lattice type and any notion of structure-preservation whatsoever on equivalences
into that carrier space, the type of structure-preserving equivalences is empty.
This is a type-level bijection-existence statement, not a claim about any specific
PDE or continuum field — it says no countable lattice can be put in bijection with
this carrier space at all, structure-preserving or not, independently of anything
a Navier-Stokes solution's velocity field would need to satisfy on that space. -/
theorem continuous_fluid_embedding_empty
    (DiscreteLattice : Type*) [Countable DiscreteLattice]
    (PreservesStructure : (DiscreteLattice ≃ EuclideanSpace ℝ (Fin 3)) → Prop) :
    IsEmpty { f : DiscreteLattice ≃ EuclideanSpace ℝ (Fin 3) // PreservesStructure f } := by
  have h_ortho : OperationallyOrthogonal DiscreteLattice (EuclideanSpace ℝ (Fin 3)) :=
    ⟨inferInstance, uncountable_euclideanSpace3⟩
  exact isEmpty_structurePreserving_of_operationallyOrthogonal h_ortho PreservesStructure

/-- A geometric scale level `N` is valid when repeatedly halving the base length
`L₀` by a factor of `1 / √2`, `N` times, has not yet driven the resulting length
below the minimum resolvable scale `h_min`. -/
def ValidLevel (L₀ h_min : ℝ) (N : ℕ) : Prop :=
  h_min ≤ L₀ * (1 / Real.sqrt 2) ^ N

/-- The set of valid geometric scale levels is finite. Since `1 / √2 ∈ (0, 1)`,
`exists_pow_lt_of_lt_one` gives a level `N₀` past which `(1/√2)^N` is already
below `h_min / L₀`; monotone decay of the power (`pow_le_pow_of_le_one`) then
shows every larger `N` fails `ValidLevel`, so the valid levels are exactly a
subset of `{0, …, N₀ - 1}`. -/
theorem validLevel_finite {L₀ h_min : ℝ} (hL : 0 < L₀) (h_min_pos : 0 < h_min) :
    {N : ℕ | ValidLevel L₀ h_min N}.Finite := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1_lt_sqrt2 : (1 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hr_nonneg : (0 : ℝ) ≤ 1 / Real.sqrt 2 := le_of_lt (div_pos one_pos hsqrt2_pos)
  have hr_lt_one : (1 / Real.sqrt 2 : ℝ) < 1 := (div_lt_one hsqrt2_pos).mpr h1_lt_sqrt2
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (div_pos h_min_pos hL) hr_lt_one
  have hsubset : {N : ℕ | ValidLevel L₀ h_min N} ⊆ {N : ℕ | N < N₀} := by
    intro N hN
    by_contra hlt
    have hge : N₀ ≤ N := not_lt.mp hlt
    have hpow_le : (1 / Real.sqrt 2 : ℝ) ^ N ≤ (1 / Real.sqrt 2) ^ N₀ :=
      pow_le_pow_of_le_one hr_nonneg hr_lt_one.le hge
    have hpow_lt : (1 / Real.sqrt 2 : ℝ) ^ N < h_min / L₀ := lt_of_le_of_lt hpow_le hN₀
    have hfinal : L₀ * (1 / Real.sqrt 2) ^ N < h_min := by
      rw [mul_comm]
      exact (lt_div_iff₀ hL).mp hpow_lt
    exact absurd hN (not_le.mpr hfinal)
  exact (Set.finite_lt_nat N₀).subset hsubset

/-- Immediate corollary of `validLevel_finite`: the subtype of valid geometric
scale levels is a `Fintype`. -/
noncomputable def validLevel_fintype {L₀ h_min : ℝ} (hL : 0 < L₀)
    (h_min_pos : 0 < h_min) : Fintype {N : ℕ // ValidLevel L₀ h_min N} :=
  have : Finite {N : ℕ // ValidLevel L₀ h_min N} :=
    (validLevel_finite hL h_min_pos).to_subtype
  Fintype.ofFinite _

/-- The `N`-indexed geometric refinement spacing at base length `L₀`: the
lattice spacing remaining after `N` halvings by `1 / √2`. `ValidLevel L₀ h_min N`
is, by definition, exactly `h_min ≤ h_seq L₀ N` (see `validLevel_iff_h_seq_le`). -/
noncomputable def h_seq (L₀ : ℝ) (N : ℕ) : ℝ := L₀ * (1 / Real.sqrt 2) ^ N

theorem validLevel_iff_h_seq_le {L₀ h_min : ℝ} {N : ℕ} :
    ValidLevel L₀ h_min N ↔ h_min ≤ h_seq L₀ N := Iff.rfl

/-- `N` is *the* maximum geometric refinement level that is still no finer than
the resolution floor `h_min`: refining one step further (to `N + 1`) would drop
the lattice spacing below `h_min`. -/
def IsMaxValidLevel (L₀ h_min : ℝ) (N : ℕ) : Prop :=
  ValidLevel L₀ h_min N ∧ ∀ N' : ℕ, ValidLevel L₀ h_min N' → N' ≤ N

/-- A maximum valid level always exists, given by an explicit, finite
computation (`Finset.max'` over the finite set `validLevel_finite` supplies),
provided the base length `L₀` starts at or above the resolution floor `h_min`
(`h_le`) — the regime in which the refinement hierarchy begins above the floor
at all, so level `0` itself is valid and the set of valid levels is nonempty as
well as finite. -/
theorem exists_isMaxValidLevel {L₀ h_min : ℝ} (hL : 0 < L₀) (h_min_pos : 0 < h_min)
    (h_le : h_min ≤ L₀) : ∃ N, IsMaxValidLevel L₀ h_min N := by
  have hfin := validLevel_finite hL h_min_pos
  have h0 : ValidLevel L₀ h_min 0 := by
    show h_min ≤ L₀ * (1 / Real.sqrt 2) ^ 0
    rw [pow_zero, mul_one]
    exact h_le
  have h0mem : (0 : ℕ) ∈ hfin.toFinset := hfin.mem_toFinset.mpr h0
  refine ⟨hfin.toFinset.max' ⟨0, h0mem⟩, ?_, ?_⟩
  · exact hfin.mem_toFinset.mp (Finset.max'_mem hfin.toFinset ⟨0, h0mem⟩)
  · intro N' hN'
    exact Finset.le_max' hfin.toFinset N' (hfin.mem_toFinset.mpr hN')

/-- At the maximum still-valid geometric refinement level `N_max` — the finest
resolution that has not yet dropped below the floor `h_min`, and which
`exists_isMaxValidLevel` shows is realized at a finite, explicitly computable
step — `discrete_lattice_prevents_gradient_blowup` gives the discrete gradient
bound `2√E_total / h_seq L₀ N_max`. This is the tightest bound in the family
`{2√E_total / h_seq L₀ N : N valid}`, since `N_max` has the smallest spacing
among valid levels. -/
theorem gradient_bound_at_max_valid_level
    {L₀ h_min : ℝ} (h_min_pos : 0 < h_min)
    {N_max : ℕ} (hN_max : IsMaxValidLevel L₀ h_min N_max)
    (NodeSpace : Type*) [MetricSpace NodeSpace]
    (h_discrete : ∀ x y : NodeSpace, x ≠ y → h_seq L₀ N_max ≤ dist x y)
    (u : NodeSpace → ℝ) (E_total : ℝ) (hE : 0 ≤ E_total)
    (h_energy : ∀ x : NodeSpace, (u x) ^ 2 ≤ E_total) :
    ∀ x y : NodeSpace, x ≠ y →
      |u x - u y| / dist x y ≤ 2 * Real.sqrt E_total / h_seq L₀ N_max := by
  have h_seq_pos : 0 < h_seq L₀ N_max :=
    lt_of_lt_of_le h_min_pos (validLevel_iff_h_seq_le.mp hN_max.1)
  exact discrete_lattice_prevents_gradient_blowup NodeSpace (h_seq L₀ N_max) h_seq_pos
    h_discrete u E_total hE h_energy

/-- Corollary of `gradient_bound_at_max_valid_level`, restated purely in terms
of the fixed resolution floor `h_min`: since the maximal valid level's spacing
is by definition no finer than the floor (`h_min ≤ h_seq L₀ N_max`), the
gradient bound achieved at that finite, computable step is in particular no
worse than `2√E_total / h_min`. -/
theorem gradient_bound_le_of_max_valid_level
    {L₀ h_min : ℝ} (h_min_pos : 0 < h_min)
    {N_max : ℕ} (hN_max : IsMaxValidLevel L₀ h_min N_max)
    (NodeSpace : Type*) [MetricSpace NodeSpace]
    (h_discrete : ∀ x y : NodeSpace, x ≠ y → h_seq L₀ N_max ≤ dist x y)
    (u : NodeSpace → ℝ) (E_total : ℝ) (hE : 0 ≤ E_total)
    (h_energy : ∀ x : NodeSpace, (u x) ^ 2 ≤ E_total) :
    ∀ x y : NodeSpace, x ≠ y →
      |u x - u y| / dist x y ≤ 2 * Real.sqrt E_total / h_min := by
  have hstep := gradient_bound_at_max_valid_level h_min_pos hN_max NodeSpace h_discrete
    u E_total hE h_energy
  have h_ge : h_min ≤ h_seq L₀ N_max := validLevel_iff_h_seq_le.mp hN_max.1
  intro x y hxy
  have hnum_nonneg : (0 : ℝ) ≤ 2 * Real.sqrt E_total := by positivity
  calc |u x - u y| / dist x y
      ≤ 2 * Real.sqrt E_total / h_seq L₀ N_max := hstep x y hxy
    _ ≤ 2 * Real.sqrt E_total / h_min := by gcongr

end Theta0Photon.NavierStokesBridge
