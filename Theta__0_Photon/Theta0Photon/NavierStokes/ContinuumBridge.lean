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

end Theta0Photon.NavierStokesBridge
