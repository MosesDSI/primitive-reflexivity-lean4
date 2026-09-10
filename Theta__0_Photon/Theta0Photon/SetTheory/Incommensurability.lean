import Theta0Photon.Algebra.GaloisGroup
import Mathlib.Analysis.Real.Cardinality

/-!
# Incommensurability: No Structure-Preserving Bijection Between a Countable and an Uncountable Type

**A scope note, upfront, in the same spirit as this session's other honesty
notes:** none of "operationally orthogonal," "`PreservesStructure`," or
"discrete count / continuous measure" are pre-existing Mathlib (or standard
mathematical) terms — they are the framework's vocabulary, and this file has
to *choose* a precise formal meaning for each rather than inherit one. The
choices made here, stated plainly rather than left implicit:

* **"Discrete count" / "continuous measure"** → `Countable A` / `Uncountable B`
  (real Mathlib typeclasses: `Uncountable` is literally `¬Countable`, from
  `Mathlib.Data.Countable.Defs`). `OperationallyOrthogonal` below is exactly
  this pair, bundled under the requested name.
* **The theorem is proved for *any* `PreservesStructure` predicate whatsoever**
  (§1, `no_structure_preserving_equiv`), not one specific chosen definition —
  because the reason it holds has nothing to do with what "structure" means.
  `A ≃ B` itself is already empty (a countable type and an uncountable type
  have no bijection between them at all, by a cardinality argument — Mathlib's
  `Function.Injective.countable`/`Uncountable.not_countable`, no auxiliary
  map construction beyond the equiv's own inverse, which is the "without an
  intermediate operator" reading used here). Restricting to a subtype with an
  extra property can only shrink an already-empty type. Picking one specific
  `PreservesStructure` (§2 uses `Monotone`, since `ℕ` and `ℝ` both carry a
  natural order) and presenting *that* instance as the interesting content
  would misstate what's actually driving the result — so the general fact is
  proved first, and the concrete instantiation is presented explicitly as a
  corollary of it, not as a separate achievement.
* **"Non-zero quotient spaces… in our field tower"** → connected explicitly
  in §3 via the field `K = ℚ(√2,√3)` from `GaloisGroup.lean`: `finrank ℚ K = 4`
  (proved there, and reused here, not re-derived) gives a `ℚ`-linear
  coordinate identification `K ≃ₗ[ℚ] (Fin 4 → ℚ)` — literally the *nonzero*
  dimension already verified — from which `K` inherits countability (`ℚ` is
  countable, a finite product of countable types is countable). `K` is
  therefore a genuine instance of the countable side of this file's theorem,
  with `ℝ` (the field it lives inside) on the uncountable side. This is the
  interpretation of "quotient space" used: each layer of the tower is
  (isomorphic to) a polynomial quotient `F[X]/(minpoly)` of *nonzero* degree
  (`natDegree_X_pow_sub_C` — degree 2 at each step, matching
  `sqrt2_finrank`/`sqrt3_finrank_over_sqrt2`), and it is exactly that nonzero,
  finite dimension that makes `K` countable rather than continuum-sized.
-/

open Polynomial IntermediateField

/-! ## §1 — The general fact, for any notion of "structure-preserving" -/

/-- The framework's hypothesis, formalized: `A` is countable ("discrete
count"), `B` is uncountable ("continuous/topological measure"). Genuinely a
`Prop`-bundle here (not a class) so it can be discharged by ordinary
instances at the call site, matching how `Countable`/`Uncountable` are used
everywhere else in Mathlib. -/
def OperationallyOrthogonal (A B : Sort*) : Prop := Countable A ∧ Uncountable B

/-- **No bijection at all exists** between a countable and an uncountable
type — proved directly from the equiv's own inverse (`f.symm : B → A`,
injective since `f` is a bijection), with no intermediate map constructed:
if `B` had an injection into the countable `A`, `B` would itself be countable
(`Function.Injective.countable`), contradicting `Uncountable B`. -/
theorem isEmpty_equiv_of_operationallyOrthogonal {A B : Type*}
    (h : OperationallyOrthogonal A B) : IsEmpty (A ≃ B) := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun f => ?_⟩
  exact hB.not_countable f.symm.injective.countable

/-- **The requested theorem, in full generality.** For *any* predicate
`PreservesStructure` on equivalences `A ≃ B` whatsoever — not one specific
choice — if `A` and `B` are operationally orthogonal, the type of
structure-preserving bijections is empty. This holds for the same reason
regardless of what "structure-preserving" means: `{f // P f}` is a subtype
of `A ≃ B`, and that ambient type is already empty
(`isEmpty_equiv_of_operationallyOrthogonal`) — no intermediate operator
bridging `A` and `B` is used or needed. -/
theorem isEmpty_structurePreserving_of_operationallyOrthogonal {A B : Type*}
    (h : OperationallyOrthogonal A B) (PreservesStructure : (A ≃ B) → Prop) :
    IsEmpty { f : A ≃ B // PreservesStructure f } :=
  haveI := isEmpty_equiv_of_operationallyOrthogonal h
  inferInstance

/-! ## §2 — The concrete instance: `A = ℕ` (discrete count), `B = ℝ` (continuous measure) -/

/-- A concrete, genuine (not vacuous-by-construction) notion of
structure-preservation for this pair: both `ℕ` and `ℝ` carry a natural
linear order, so "preserves structure" is taken here to mean order-preserving. -/
def PreservesStructure (f : ℕ ≃ ℝ) : Prop := Monotone f

theorem operationallyOrthogonal_nat_real : OperationallyOrthogonal ℕ ℝ :=
  ⟨inferInstance, inferInstance⟩

/-- **The requested statement, concretely.** No monotone bijection between
`ℕ` and `ℝ` exists. As the general theorem above makes explicit, this is
true for the same reason `IsEmpty (ℕ ≃ ℝ)` is true — `Monotone` plays no
special role; any other predicate would give the same conclusion, for the
same reason. -/
theorem isEmpty_monotone_equiv_nat_real :
    IsEmpty { f : ℕ ≃ ℝ // PreservesStructure f } :=
  isEmpty_structurePreserving_of_operationallyOrthogonal operationallyOrthogonal_nat_real _

/-! ## §3 — Connecting to the field tower: `K = ℚ(√2,√3)` is on the countable side -/

/-- `K`'s coordinate identification with `Fin (finrank ℚ K) → ℚ`, using the
*nonzero* dimension `sqrt2_sqrt3_finrank : finrank ℚ K = 4` verified in
`GaloisGroup.lean` (built on `FieldTower.lean`'s closed degree-4 tower) — not
re-derived here, only reused. This is the file's literal cash-out of
"non-zero quotient spaces… in the field tower": each layer of that tower is
(isomorphic to) a polynomial quotient of nonzero degree, and it is exactly
that finite, nonzero dimension that identifies `K` with a finite power of
`ℚ` here. -/
noncomputable def kCoordEquiv : K ≃ₗ[ℚ] (Fin (Module.finrank ℚ K) → ℚ) :=
  (Module.finBasis ℚ K).equivFun

/-- **`K` is countable** — transported along `kCoordEquiv` from `Fin 4 → ℚ`
(a finite product of the countable `ℚ`), using the field tower's own
already-verified dimension, not an assumed one. -/
instance : Countable K := Countable.of_equiv _ kCoordEquiv.symm.toEquiv

/-- **The field tower, as a genuine instance of §1's theorem.** `K` (built
today, `[K:ℚ] = 4`) and `ℝ` (the ambient field `K` lives inside) are
operationally orthogonal — `K` countable via its finite dimension, `ℝ`
uncountable — so no bijection of any kind exists between them, structure-
preserving or not. This is not a re-statement of `K ⊊ ℝ` (a strict subfield
inclusion, already implicit in `K`'s very definition as an `IntermediateField
ℚ ℝ`): it is the sharper, size-theoretic fact that `K` and `ℝ` cannot be put
in bijection *at all*, which does not follow from `K` merely being a proper
subfield (proper subfields can still have the same cardinality as the whole
field — this failure is specific to `K` being finite-dimensional, hence
countable). -/
theorem isEmpty_equiv_K_real : IsEmpty (K ≃ ℝ) :=
  isEmpty_equiv_of_operationallyOrthogonal ⟨inferInstance, inferInstance⟩
