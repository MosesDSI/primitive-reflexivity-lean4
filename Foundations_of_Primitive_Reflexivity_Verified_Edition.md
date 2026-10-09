# Foundations of Primitive Reflexivity

### The Discrete Node-First Ontology, Axis Incommensurability, and the Phase-Drift Definition of Angles

**Verified Edition, Revision 3: every mathematical claim backed by a Lean 4 proof**
Jonathon Pearson · September 2026
[github.com/MosesDSI/primitive-reflexivity-lean4](https://github.com/MosesDSI/primitive-reflexivity-lean4)

> This is the canonical, GitHub-renderable edition of this paper. A `.docx` copy
> (Revision 2) also exists in the repository root for offline/Word use; this file
> is the one kept current, since it renders in-browser here and its citations are
> live links into the code. Revision 3 adds `PhantomFixedField.lean` and
> `PhantomTriadicBridge.lean` (§11.6, §11.10), which postdate Revision 2.

---

## Abstract

This edition restates the foundations of primitive reflexivity so that every
mathematical claim corresponds to a machine-checked Lean 4 theorem. We work with
a type of nodes `N` carrying a relation `ℛ` that is reflexive at every node, and
verify that this diagonal self-relation is dominated by every other reflexive
relation, is transported by every bijection, and keeps its truth value when `ℛ`
is decorated with a metric, a partial order, or an algebraic operation. In
arithmetic, we verify that primality is equivalent to having divisor set exactly
`{1, p}`.

We verify the incommensurability of the two axes in two forms. Geometrically,
the Manhattan step `1 + 1` is rational while the diagonal `√(1²+1²) = √2` is not,
so no rational measures the diagonal and the gap `2 − √2` is positive; the
square's boundary also unfolds isometrically onto an interval of length `4s`.
Algebraically, `(ℝ, +)` is not isomorphic to the circle group `U(1)`, because
`U(1)` contains an element of order 2 while `ℝ` is torsion-free, and no integer
equals a nonzero integer multiple of the rotational period `2π`.

We formalize the phase-drift definition of an angle as a predicate on
bifurcated Polar/Axial clock states and prove that a fixed-increment Axial
clock never closes the `√2` diagonal gap. We prove that a number system
containing a square root of 2 admits no order-preserving map back onto `ℚ`
that fixes the rationals, and construct `ℚ(√2)` from scratch as a
kernel-checked ordered field with rational density. We verify the arithmetic
of the triadic state `(n, √n, n²)`: the geometric-mean bridge
`√(n · n²) = n√n`, strict positivity of the mediator defect
`√n + √m − √(n+m)`, and the equipartition identity
`cos²(π/4) = sin²(π/4) = 1/2`. The triad is closed exactly under componentwise
multiplication but not addition, and the classical count `n` is its
projection, with the discarded part equal to the mediator defect.

We further verify the algebraic ground of the framework: `x² − n` is
irreducible over `ℚ` for every non-square `n`, each `ℚ(√n)` has degree 2,
`ℚ(√2,√3)` has degree 4 with Galois group the Klein four-group, and permuting
the rows of a 3×3 triadic matrix scales its determinant by the permutation's
sign. **New in Revision 3:** the Klein four-group's non-identity "Phantom
Middle" element is shown to fix *exactly* the product `√2·√3`, to be the
unique non-identity automorphism doing so, and to act on the triadic states of
`2` and `3` in line with the split the triad itself draws between exact
multiplicative closure and defective additive closure — it fixes the product
coordinate `√2·√3` and reverses the sum coordinate `√2+√3`. (This is proved for
the pair `(2,3)` only; see §11.10 for its scope.) Finally, we verify that discrete and continuum are
operationally orthogonal: no bijection of any kind exists between a countable
carrier and `ℝ` or `ℝ³`, while on a lattice with minimum spacing difference
quotients stay uniformly bounded and geometric refinement by `1/√2` has only
finitely many valid levels.

---

## 1. Introduction and Verification Scope

The original version of this paper combined formal mathematics with
ontological interpretation. This edition keeps only the mathematical claims
that have been proved in Lean 4, states each one exactly as the Lean theorem
states it, and cites the Lean declaration and file beneath it. Interpretive
readings of the formal objects are retained where they help, but they are set
apart as **Interpretation** and are not claims of the formalization. Claims
from the original draft that have no Lean counterpart (Axiom R2, the
`σ = 1/2` calibration argument, and the frequency-ratio reading of angle) are
omitted.

The results are checked at two tiers, summarized in the table below. Revision
2 added the companion project `Theta__0_Photon/`. Revision 3 adds
`PhantomFixedField.lean` and `PhantomTriadicBridge.lean` to it. All paths are
relative to `PrimitiveReflexivity/` unless they name a top-level folder. A
repository-wide scan of all tracked `.lean` files finds no `sorry`,
`native_decide`, `axiom`, `unsafe`, or `implemented_by`.

**Environment:** Lean `v4.33.1`, Mathlib rev `0df444a3`. The ordered-field
milestone is tagged `v1.0-qs-ordered-field`.

| Tier | Files | How checked | Trust footprint |
|---|---|---|---|
| 1 (Mathlib) | `Foundations.lean`, `Geometry/SquareUnfolding.lean`, `Discrete/HarmonicCenter.lean` | `lake build` against Mathlib; CI runs the same build on every push | `[propext, Classical.choice, Quot.sound]`, audited by `AxiomCheck.lean` |
| 1 (bare Lean in library) | `Discrete/OrderObstruction.lean` | `lake build`, standalone `lean`, and independent `leanchecker` replay | `[propext, Classical.choice, Quot.sound]` |
| 1 (Mathlib, companion project) | `Theta__0_Photon/`: `Basic`, `Main`, `GroundAxiom`, `FieldTower`, `GaloisGroup`, `PhantomFixedField`, `PhantomTriadicBridge`, `ChiralSign`, `TriadicClosure`, `UniquenessTest`, `Incommensurability`, `ContinuumBridge`, `CenteredKernel` | Its own `lake build` against the same Mathlib; CI on every push | `[propext, Classical.choice, Quot.sound]`, per-file `#print axioms` |
| 2 (standalone) | `R3_bare_lean/`, `Section_VI_Incommensurability/` | Each file checked with `lean <file>`; not part of `lake build` or CI | R3 files: no axioms at all |

## 2. Primitive Setup: Reflexive Structure on a Node Field

*Verification scope. Tier 1, [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean).*

**Definition 2.1 (Node Field).** A node field is an arbitrary type `N`. No
metric, order, topology or arithmetic is assumed on `N`.
Lean: `variable {N : Type}` · [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)

**Definition 2.2 (Primitive Reflexive Operator).** A primitive reflexive
operator is a binary relation `ℛ : N → N → Prop`.
Lean: `variable (R : N → N → Prop)` · [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)

**Axiom R1 (Localized Reflexivity).** The relation `ℛ` is localized-reflexive
if every node is related to itself: `∀ x ∈ N, x ℛ x`.
Lean: `class LocalizedReflexive` · [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)

**Theorem 2.3 (Diagonal Minimality).** Let `ℛ` be localized-reflexive and let
`S` be any relation on `N` with `∀x, x S x`. Then for every node `x`,
`x ℛ x ⟹ x S x`.
Lean: `reflexive_minimality` · [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)

**Theorem 2.4 (Diagonal Transport).** Let `ℛ₁` on `N₁` and `ℛ₂` on `N₂` be
localized-reflexive and let `f : N₁ ≃ N₂` be a bijection. Then for every
`x ∈ N₁`: `x ℛ₁ x ⟺ f(x) ℛ₂ f(x)`.
Lean: `reflexive_isomorphism` · [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)

Both theorems concern the diagonal pairs `(x, x)`, which is exactly where
localized reflexivity lives; they make no claim about pairs of distinct nodes.
Theorem 2.3 records that the diagonal `{(x,x)}` is contained in every
reflexive relation `S` on `N`, i.e. that it is their common lower bound.

**Definition 2.5 (Local Nodes).** In the companion project, a node carries a
natural-number identifier and `ℛ` is equality: `x ℛ y :⟺ x = y`. A node is
therefore related to itself and to nothing else.
Lean: `Node`, `R` · [`Theta0Photon/Basic.lean`](Theta__0_Photon/Theta0Photon/Basic.lean)

> **Interpretation.** `x ℛ x` is the per se identity of a node: its
> self-coherence prior to any external observer, clock or ruler. Theorem 2.3
> says no reflexive relation can hold less of this self-identity than `ℛ`
> does, and Theorem 2.4 says it is preserved under any relabelling of the
> nodes.

## 3. A-Metric Independence (Axiom R3)

*Verification scope. Theorems 3.1–3.4: Tier 2, [`R3_bare_lean/`](R3_bare_lean/).
Theorems 3.5–3.6: Tier 1, [`Theta__0_Photon/`](Theta__0_Photon/). Each R3 file
compiles standalone in bare Lean 4 with no axioms. Each proof uses exactly one
reflexivity-shaped property of the added structure (`d(x,x)=0`, `x≤x`, or
`m∘0=m`) and never uses the others (symmetry, triangle inequality,
transitivity, antisymmetry).*

In each theorem, `ℛ` is decorated by pairing it with an external structure.
The result is that on the diagonal the decorated relation is equivalent to
plain `ℛ`, so adding the structure does not change the truth value of `x ℛ x`.

**Theorem 3.1 (Metric Independence).** Let `d` be a `ℕ`-valued metric on `N`
(with `d(x,x)=0`, symmetry and the triangle inequality), and let `P` be a
predicate on `ℕ` with `P(0)`. Define `x ℛ_d y :⟺ x ℛ y ∧ P(d(x,y))`. Then
`∀x, x ℛ_d x ⟺ x ℛ x`.
Lean: `metric_independence` · [`R3_metric.lean`](R3_bare_lean/R3_metric.lean)

**Theorem 3.2 (Order Independence).** Let `≤` be a partial order on `N` and
define `x ℛ_≤ y :⟺ x ℛ y ∧ x ≤ y`. Then `∀x, x ℛ_≤ x ⟺ x ℛ x`.
Lean: `a_metric_independence_order` · [`R3_order.lean`](R3_bare_lean/R3_order.lean)

**Theorem 3.3 (Algebraic Independence).** Let `M` carry an operation `∘` with
an element `0` satisfying `m∘0=m`, and let `e : N → M`. Define
`x ℛ_∘ y :⟺ x ℛ y ∧ e(x)∘0 = e(x)`. Then `∀x, x ℛ_∘ x ⟺ x ℛ x`.
Lean: `a_metric_independence_algebraic` · [`R3_algebraic.lean`](R3_bare_lean/R3_algebraic.lean)

**Theorem 3.4 (General Gated Decoration).** Let `e : N × N → M` and let `P`
be a predicate on `M` with `P(e(x,x))` for all `x`. Define
`x ℛ_e y :⟺ x ℛ y ∧ P(e(x,y))`. Then `∀x, x ℛ_e x ⟺ x ℛ x`.
Lean: `a_metric_independence_v2` · [`R3_decorated.lean`](R3_bare_lean/R3_decorated.lean)

**Theorem 3.5 (Zero Is Not a Coordinate).** For local nodes (Definition 2.5),
any `ℕ`-valued metric `d` and any predicate `P` with `P(0)`:
`x ℛ_d x ⟺ x ℛ x` for every node `x`.
Lean: `zero_is_not_a_coordinate` · [`Main.lean`](Theta__0_Photon/Main.lean)

**Theorem 3.6 (Strict Metrics See Exactly the Diagonal).** Call `d` strict if
every pair of distinct nodes has positive distance. Then no distinct pair has
distance 0, and for all nodes `d(x,y) = 0 ⟺ x ℛ y`.
Lean: `off_diagonal_dist_ne_zero`, `dist_eq_zero_iff_R` · [`Theta0Photon/Basic.lean`](Theta__0_Photon/Theta0Photon/Basic.lean)

> **Interpretation.** Intrinsic identity is scale-free: a node's
> self-coherence is fixed internally and does not depend on external rulers,
> orderings or operations. Theorems 3.1–3.4 hold by construction once the
> decoration is stipulated to be neutral on the diagonal (`d(x,x)=0`,
> `x≤x`, `m∘0=m`, or `P(e(x,x))`); 3.4 subsumes 3.1–3.3. What the
> formalization contributes is that these standard decorations do satisfy the
> hypothesis, and, in 3.6, that a strict metric detects exactly the diagonal.
> The folder also contains
> [`R3_tautological.lean`](R3_bare_lean/R3_tautological.lean), a control
> showing that the undecorated statement is trivial.

## 4. Arithmetic Descent: Primes as Per Se Identity

*Verification scope. Tier 1, [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean).*

**Definition 4.1 (Divisor Set).** For `p ∈ ℕ`, `Div(p) = {d ∈ ℕ : d ∣ p}`.
Lean: `DivSet`

**Definition 4.2 (Arithmetic Per Se Identity).** A natural number `p` is an
arithmetic per se identity if `p > 1` and `Div(p) = {1, p}`.
Lean: `ArithmeticPerSeIdentity`

**Theorem 4.3 (Prime Incompressibility).** For every `p ∈ ℕ`:
`p is prime ⟺ p > 1 ∧ Div(p) = {1, p}`.
Lean: `prime_incompressibility`

> **Interpretation.** A prime is the arithmetic realization of per se
> identity: its divisor set is as small as possible, with no intermediate
> mediator between 1 and itself.

## 5. Geometric Incommensurability on the Square

*Verification scope. Tier 1, [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)
(5.1) and [`Geometry/SquareUnfolding.lean`](PrimitiveReflexivity/Geometry/SquareUnfolding.lean) (5.2).*

### 5.1 Manhattan step and diagonal step

**Definition 5.1.** The Manhattan step is `P = 1+1`. The diagonal step is
`D = √(1²+1²)`. One checks `D = √2`.
Lean: `manhattan_step`, `diagonal_step`, `diagonal_eq_sqrt_two`

**Theorem 5.2 (Manhattan Step is Rational).** There is `q ∈ ℚ` with `q = P`.
Lean: `manhattan_is_rational`

**Theorem 5.3 (Diagonal Step is Irrational).** `D` is irrational.
Lean: `diagonal_is_irrational`

**Theorem 5.4 (No Common Rational Measure).** There is no `q ∈ ℚ` with `q = D`.
Lean: `no_common_rational_measure`

**Theorem 5.5 (Positive Gap).** `Δ_gap = P − D = 2 − √2 > 0` (`≈ 0.58579`).
Lean: `delta_gap_pos`

### 5.2 Unfolding the boundary of the square

Consider the square `[0,s]×[0,s]`. Its boundary has four directed edges in
cyclic order (bottom, right, top, left, indices 0–3); edge `e` has
`off(e) = index(e)·s`. A boundary point `(e,t)` (`0≤t≤s`) unfolds to
`unfold(e,t) = off(e)+t`. The perimeter is `4s`.

**Theorem 5.6 (Unfolding Bounds).** If `s ≥ 0`, every boundary point
satisfies `0 ≤ unfold(e,t) ≤ 4s`.
Lean: `unfold_bounds` · [`SquareUnfolding.lean`](PrimitiveReflexivity/Geometry/SquareUnfolding.lean)

**Theorem 5.7 (Isometry Along an Edge).** For points on the same edge,
`unfold(e,t₂) − unfold(e,t₁) = t₂ − t₁`.
Lean: `unfold_isometry_same_edge`

**Theorem 5.8 (Corner Adjacency).** `off(bottom)+s = off(right)`,
`off(right)+s = off(top)`, `off(top)+s = off(left)`.
Lean: `unfold_corner_adjacency`

**Theorem 5.9 (Perimeter Conservation).** `off(left) + s = 4s`.
Lean: `perimeter_unfold_conservation`

### 5.3 The two diagonals of the square

*Verification scope. Tier 1, [`Statistics/CenteredKernel.lean`](Theta__0_Photon/Theta0Photon/Statistics/CenteredKernel.lean).*

In the two-cell model, the main diagonal is `D1=(1,1)` and the anti-diagonal
is `D2=(1,−1)`. A sample `s=(s1,s2)` has mean `s̄=(s1+s2)/2`.

**Theorem 5.10 (Orthogonal Diagonals).** `D1·D2 = 1·1 + 1·(−1) = 0`.
Lean: `square_diagonals_orthogonal`

**Theorem 5.11 (The Anti-Diagonal is Centered).** The entries of `D2` sum to 0.
Lean: `d2_in_centered_subspace`

**Theorem 5.12 (Every Pair Splits Along the Two Diagonals).**
`s = s̄·D1 + (s1−s̄, s2−s̄)`.
Lean: `sample_decomp_two`, `two_cell_direct_sum`

**Theorem 5.13 (General Dimension).** For samples with `N ≥ 1` entries, the
diagonal (constant) subspace and the centered subspace are complementary, and
the centered subspace has dimension `N−1`. Deviations from the mean always
sum to 0.
Lean: `sample_space_direct_sum`, `finrank_centeredSubspace`, `deviations_sum_zero`

> **Interpretation.** Sequential traversal of the square is exactly additive
> and lands on rational measures (5.2, 5.6–5.9). Simultaneous co-traversal of
> both steps forces the diagonal, which no rational subdivision can measure
> (5.3–5.4). The positive gap `2−√2` is the geometric residue left between
> the two. The two diagonals are not interchangeable in role: the main
> diagonal carries the shared mean of a pair, the anti-diagonal carries its
> signed difference, and every pair is exactly the sum of the two (5.12).

## 6. Algebraic Incommensurability in the Complex Plane

*Verification scope. Tier 1, [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean).
`Circle` is Mathlib's group of unit complex numbers, i.e. `U(1)`.*

**Theorem 6.1 (Group Inequivalence).** There is no bijection `f : ℝ → U(1)`
with `f(x+y) = f(x)·f(y)` for all `x,y`.
Lean: `group_inequivalence`

*Proof idea (as formalized).* Such an `f` would satisfy `f(0)=1`. Choose `r`
with `f(r)=−1`. Then `f(2r)=(−1)²=1=f(0)`, so injectivity gives `2r=0`, hence
`r=0` and `−1=f(0)=1`, a contradiction. The argument uses only torsion:
`U(1)` has an element of order 2 and `(ℝ,+)` has none.

**Corollary 6.2 (ℝ ≇ U(1)).** `(ℝ,+)` and `U(1)` are not isomorphic as groups.
Lean: `real_not_equiv_circle`

Because the proof uses torsion rather than topology, the two groups are
non-isomorphic as *abstract* groups, not only as topological groups.

**Theorem 6.3 (Irrational Period).** `2π` is irrational.
Lean: `two_pi_irrational`

**Theorem 6.4 (Period Incommensurability).** There are no integers `m,n` with
`n≠0` and `m·1 = n·2π`.
Lean: `period_incommensurability`

> **Interpretation.** The horizontal axis carries additive, torsion-free
> translation; the rotational axis carries a periodic structure with
> torsion. No isomorphism identifies them, and the rotational period `2π`
> shares no integer measure with the unit step.

## 7. The Dual-Clock Engine and the Phase-Drift Angle

*Verification scope. Tier 2, [`Section_VI_dual_clock.lean`](R3_bare_lean/Section_VI_dual_clock.lean)
and [`Section_VI_Incommensurability/`](Section_VI_Incommensurability/). These
files work with an abstract clock model; connecting it to the concrete
geometry of Sections 5–6 is not part of the formalization.*

**Definition 7.1 (Bifurcated State).** A bifurcated state over a phase type
`Φ` is a pair `(C_pol, C_ax)` with `C_pol ∈ ℕ` (the Polar clock, counting
discrete ticks) and `C_ax ∈ Φ` (the Axial clock, holding a phase).
Lean: `BifurcatedState`

**Definition 7.2 (Axial Rotation).** An axial rotation on `Φ` is a map
`ρ : Φ → Φ`, one rotation step per Polar tick.
Lean: `AxialRotation`

**Definition 7.3 (Phase-Drift Angle).** A target phase `θ ∈ Φ` is the
phase-drift angle of a state `(C_pol, C_ax)` when applying the Axial rotation
once per Polar tick carries the Axial clock exactly to `θ`:
`PhaseDriftMatch((C_pol,C_ax), θ) :⟺ ρᵏ(C_ax) = θ` where `k = C_pol`.
Lean: `PhaseDriftMatch`

This predicate is checked to be non-vacuous: with `Φ=ℕ` and `ρ(x)=x+1`, it
holds for 3 ticks from 0 to target 3 and fails for target 7. It also
elaborates identically with and without automatic implicit arguments.

**Theorem 7.4 (Polar/Axial Incommensurability).** There are no natural
numbers `m,n` with `n≠0` and `m²=2n²`. Equivalently, with the Polar step
fixed at 1, no Polar tick count and integer Axial count satisfy the diagonal
closure relation. Proved by infinite descent over `ℕ`, without real numbers.
Lean: `no_sqrt2_aux`, `polar_axial_incommensurable` · [`Polar_Axial_Incommensurability.lean`](Section_VI_Incommensurability/Polar_Axial_Incommensurability.lean)

**Theorem 7.5 (Fixed-Step Reach).** With `Φ=ℕ` and the fixed-increment
rotation `ρ(x)=x+c`, a state starting at phase 0 reaches phase `nc` after `n`
Polar ticks: `PhaseDriftMatch((n,0), nc)`.
Lean: `const_step_reaches` · [`Axial_Divergence_Theorem.lean`](Section_VI_Incommensurability/Axial_Divergence_Theorem.lean)

**Theorem 7.6 (Axial Divergence).** For every step size `c ∈ ℕ` and every
`n≠0`, the Axial clock provably reaches phase `nc` after `n` Polar ticks, and
that phase never closes the diagonal gap:
`PhaseDriftMatch((n,0), nc)` and `(nc)² ≠ 2n²`.
Lean: `axial_clock_never_closes_the_diagonal_gap` · [`Axial_Divergence_Theorem.lean`](Section_VI_Incommensurability/Axial_Divergence_Theorem.lean)

> **Interpretation.** An angle is the internal phase drift between the Polar
> clock (discrete translation) and the Axial clock (rotation) of a node
> establishing orientation. Theorem 7.6 shows the Axial clock, ticking in
> step with the Polar clock, always reaches a definite phase that can never
> match the `√2` ratio of the diagonal. The drift between the two clocks
> cannot be closed.
>
> *Scope.* Theorem 7.6 is proved for `Φ=ℕ` with an integer step `c`; there
> `(nc)² = 2n²` reduces to `c² = 2`, so it restates Theorem 7.4 in the
> vocabulary of the clock model. It does not yet involve the `2π` structure of
> §6. A phase type that carries a circle (for example `ℤ/N` or `U(1)` with a
> rotation step) is where the drift of an angle would be tested against §6;
> that connection is not formalized.

## 8. Order Obstruction and the Certified Field ℚ(√2)

*Verification scope. Tier 1, [`Discrete/OrderObstruction.lean`](PrimitiveReflexivity/Discrete/OrderObstruction.lean):
bare Lean 4 with no Mathlib, built as part of the library. Axiom footprint
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, independently
replayed with `leanchecker`. At 1900+ lines, this is the largest single file
in the repository.*

### 8.1 The abstract obstruction

Let `Q` and `K` be ordered types and `ι : Q → K` an order embedding
(`a<b ⟺ ι(a)<ι(b)`). Assume `K` satisfies trichotomy and `ι(Q)` is dense in
`K`. A retraction is a map `f : K → Q` that is monotone and fixes `Q`
(`f(ι(q))=q`).

**Theorem 8.1 (Retraction is Identity).** Under these hypotheses every
retraction satisfies `ι(f(x))=x` for all `x ∈ K`.
Lean: `retraction_is_identity`

**Corollary 8.2 (Gap Blocks Retraction).** If some `x ∈ K` is not of the form
`ι(q)`, no retraction exists.
Lean: `no_retraction_if_gap`

**Lemma 8.3 (No Rational √2).** No natural numbers satisfy `p²=2q²` with
`q≠0`, and no rational `r` satisfies `r²=2`.
Lean: `no_sqrt_two_nat`, `rat_no_sqrt_two`

**Theorem 8.4 (√2 Blocks Retraction).** If `ι` is injective and
multiplicative, `K` contains `s` with `s·s=ι(2)`, and `Q` has no square root
of 2, then no retraction `K→Q` exists.
Lean: `no_order_retraction_of_sqrt_two`, `no_order_retraction_rat`

**Theorem 8.5 (Local Form).** Density and trichotomy are needed only at the
gap point.
Lean: `no_retraction_local`

**Proposition 8.6 (Necessity of the Hypotheses).** Each hypothesis is
needed — without density, without the retraction condition, or without
monotonicity, a counterexample is exhibited for each.
Lean: `density_needed`, `retract_needed`, `mono_needed`

### 8.2 The ordered field QS = ℚ(√2)

`QS` consists of pairs `(a,b)` of rationals, read as `a+b√2`, with the usual
field operations, norm `a²−2b²`, embedding `emb(q)=q+0√2`, and gap point
`s=0+1√2`.

**Theorem 8.7 (Square Root of 2).** `s·s = emb(2)`.
Lean: `s_mul_s`

**Theorem 8.8 (Field Laws).** Addition and multiplication are associative,
commutative, with identities and inverses; the norm is multiplicative,
`norm(x)=0 ⟺ x=0`.
Lean: `add_assoc … right_distrib, norm_mul, norm_eq_zero_iff, mul_inv_cancel`

**Theorem 8.9 (Ordered Field).** The order is total, transitive,
translation-invariant, and positivity is closed under `+`/`·`.
Lean: `trichotomy, transitivity, add_lt_add_left, pos_add, mul_pos`

**Theorem 8.10 (Rational Density).** For any `x<y` in `QS` there is a
rational `q` with `x < emb(q) < y`, built explicitly (no Cauchy completions),
via an iterating rational sequence converging to `√2`.
Lean: `qs_dense`

**Theorem 8.11 (Incommensurability Blocks Retraction).** There is no
monotone map `f : QS → ℚ` with `f(emb(q))=q` for all `q ∈ ℚ`.
Lean: `incommensurability_blocks_retraction`

> **Interpretation.** Once the number line contains a point incommensurable
> with the rationals, it cannot be folded back onto the rationals without
> breaking order. The diagonal of Section 5 is exactly such a point.

## 9. The Triadic State and the Mediator Defect

*Verification scope. Tier 1: [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean)
(9.1–9.5) and [`Theta0Photon/Algebra/`](Theta__0_Photon/Theta0Photon/Algebra/) (9.6–9.12).*

**Definition 9.1 (Triadic State).** For `n ∈ ℕ`:
`𝒮ₙ = (n, √n, n²)` = (polar count, axial mediator, boundary potential).
Lean: `TriadicState`

**Theorem 9.2 (Geometric-Mean Bridge).** `√(n·n²) = n√n`.
Lean: `geometric_mean_bridge`

**Definition 9.3 (Mediator Defect).** `ℰ(n,m) = √n + √m − √(n+m)`.
Lean: `mediator_defect`

**Theorem 9.4 (Positive Mediator Defect).** For all `n,m>0`: `ℰ(n,m) > 0`.
Lean: `mediator_defect_positive`

**Theorem 9.5 (Equipartition Fixed Point).**
`cos²(π/4) = sin²(π/4) = 1/2`.
Lean: `equipartition_fixed_point`

**Definition 9.6 (Typed Triadic Number).** A `TriadicNat` bundles `n ∈ ℕ`
with `polar ∈ ℚ`, `axial ∈ ℝ`, `boundary ∈ ℕ`, and invariants
`polar=n`, `axial=√n`, `boundary=n²`.
Lean: `TriadicNat`, `add_componentwise`, `mul_componentwise` · [`TriadicClosure.lean`](Theta__0_Photon/Theta0Photon/Algebra/TriadicClosure.lean)

**Theorem 9.7 (Exact Multiplicative Closure).** The componentwise product of
two triadic numbers satisfies the invariants of the product `nm`: exactly,
zero residue.
Lean: `triadic_multiplication_closed`

**Theorem 9.8 (Additive Non-Closure).** For `n,m>0`, the componentwise sum
fails the axial invariant: `√n+√m ≠ √(n+m)`.
Lean: `triadic_addition_not_closed`

**Definition 9.9 (Classical Projection).** `π(n,polar,axial,boundary) = n`.
Lean: `π`

**Theorem 9.10 (Projection Commutes on the Count).**
`n of (x⊕y) = π(x)+π(y)`.
Lean: `projection_commutes_on_n`

**Theorem 9.11 (Correction Identity).** What the projection discards is
exactly the mediator defect: `(√n+√m) − ℰ(n,m) = √(π(x)+π(y))`.
Lean: `correction_identity`

**Proposition 9.12 (Uniqueness Test).** Exact multiplicative closure and a
strictly positive additive residue alone do not single out `√n` — the
constant function `1` also satisfies both, degenerately.
Lean: `const_one_satisfies_both_conditions` · [`UniquenessTest.lean`](Theta__0_Photon/Theta0Photon/Algebra/UniquenessTest.lean)

> **Interpretation.** The triad holds the discrete count, its irrational
> mediator, and its two-dimensional boundary potential together. Additive
> composition along the mediator coordinate always leaves a strictly
> positive residue (9.4); at 45° the two orthogonal components carry equal
> weight (9.5). Classical `ℕ` is the projection `π` of the triad: it sees
> addition correctly on the count alone, and the one quantity it discards is
> the mediator defect (9.11). **§11.10 relates this split to the Galois
> group of §11 for the pair `(2,3)`: the Phantom Middle fixes the product
> coordinate `√2·√3`, where the triad closes exactly, and negates the sum
> coordinate `√2+√3`, where the defect arises. It also negates `√2` and `√3`
> individually.**

## 10. Discrete Harmonic Centers

*Verification scope. Tier 1, [`Discrete/HarmonicCenter.lean`](PrimitiveReflexivity/Discrete/HarmonicCenter.lean).*

**Definition 10.1.** For `k ∈ ℕ`, `Ω_k = {1,…,2k+1} ⊂ ℤ`, harmonic center `k+1`.
Lean: `omega`

**Theorem 10.2 (Harmonic Symmetry).** `|(k+1−j)−(k+1)| = |(k+1+j)−(k+1)|`.
Lean: `harmonic_distance_symmetry`

For `k=10`, split `{1,…,21}` into residue classes mod 3: `C1(≡1)`, `C2(≡2)`, `C3(≡0)`.

**Theorem 10.3 (Center in the Middle Class).** The center `11` lies in `C2`.
Lean: `harmonic_center_in_C2`

**Theorem 10.4 (Minimal Distance Sum).** Total distances from `11`: `37, 36,
37` for `C1,C2,C3` — the middle class has the strictly smallest sum.
Lean: `tri_partition_distance_sums`

## 11. The Algebraic Ground: Irreducibility, Field Tower, Phantom Middle, and Chiral Sign

*Verification scope. Tier 1, [`Theta0Photon/Algebra/`](Theta__0_Photon/Theta0Photon/Algebra/)
and [`Geometry/`](Theta__0_Photon/Theta0Photon/Geometry/). `ℚ(√d)` and
`ℚ(√2,√3)` are subfields of `ℝ` generated by the indicated square roots.*

**Theorem 11.1 (Ground Axiom).** Let `n ∈ ℕ` be non-square. Then `x²−n` has
no rational root and is irreducible over `ℚ`.
Lean: `triadic_no_rational_root`, `triadic_ground_irreducible` · [`GroundAxiom.lean`](Theta__0_Photon/Theta0Photon/Algebra/GroundAxiom.lean)

**Theorem 11.2 (Quadratic Degree).** For every non-square `d ∈ ℕ`,
`[ℚ(√d):ℚ] = 2`.
Lean: `sqrt_finrank` · [`FieldTower.lean`](Theta__0_Photon/Theta0Photon/Algebra/FieldTower.lean)

**Theorem 11.3 (Representation in ℚ(√2)).** Every element of `ℚ(√2)` is
`a+c√2` with `a,c ∈ ℚ`.
Lean: `sqrt2_field_eq`

**Theorem 11.4 (Field Tower).** `√3 ∉ ℚ(√2)`, and `[ℚ(√2,√3):ℚ] = 4`.
Lean: `sqrt3_notMem`, `sqrt2_sqrt3_finrank`

**Theorem 11.5 (Klein Four Galois Group).** `K = ℚ(√2,√3)` is Galois over
`ℚ`, has exactly 4 automorphisms, and its automorphism group is a Klein
four-group `ℤ/2 × ℤ/2`.
Lean: `card_Gal_eq_four`, `IsGalois` and `IsKleinFour` instances · [`GaloisGroup.lean`](Theta__0_Photon/Theta0Photon/Algebra/GaloisGroup.lean)

**Theorem 11.6 (Phantom Middle Fixes the Product).** Let `σ,τ` be the two
sign flips of `K` and `π = σ∘τ` their composite, the Phantom Middle.

(a) `π` fixes `√2·√3`, while `σ(√2·√3) = τ(√2·√3) = −√2·√3`.
(b) Among the four automorphisms of `K`, exactly `1` and `π` fix `√2·√3`.
(c) `x ∈ K` is fixed by `π` iff `x = a+b·√2·√3` for `a,b ∈ ℚ`.
(d) The fixed field of `⟨π⟩` is `ℚ(√2·√3)`.

In Revision 2 this theorem recorded only that `π` sends `√2` to `−√2`
(`phantom_middle_sqrt2`) and that `π` corresponds to `(1,1)` of `ℤ/2×ℤ/2`
(`galoisKleinFourEquiv_phantom_middle`). Revision 3 states (a)–(d) as theorems
in `PhantomFixedField.lean`; (a) follows from the earlier flip lemmas on `√2`
and `√3` by `map_mul`, but is first stated there.

Lean: `phantom_middle_fixes_sqrt6K` ([L72](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean#L72)),
`sigma_negates_sqrt6K` ([L85](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean#L85)),
`tau_negates_sqrt6K` ([L97](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean#L97)),
`stabilizer_sqrt6K` ([L111](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean#L111)),
`phantom_middle_fixed_iff` ([L222](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean#L222)),
`fixedField_phantom_middle` ([L175](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean#L175))
· [`PhantomFixedField.lean`](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean)

**Theorem 11.7 (Chiral Sign Law).** For any 3×3 matrix `M` over a
commutative ring and any permutation `σ` of its rows,
`det(σM) = sign(σ)·det(M)`.
Lean: `chiral_sign_law`, `transposition_flips_orientation`,
`even_permutation_preserves_orientation`, `fin3_isOdd_iff_isSwap` · [`ChiralSign.lean`](Theta__0_Photon/Theta0Photon/Geometry/ChiralSign.lean)

**Theorem 11.8 (The −21 Orbit Matrix).** The matrix with rows `(2,1,4)`,
`(1,2,4)`, `(2,4,1)` has determinant `−21`; swapping its last two rows gives
`+21`; rotating all three rows leaves `−21`.
Lean: `canonicalOrbitMatrix_det`, `canonicalOrbitMatrix_swap_det`, `canonicalOrbitMatrix_rotate_det`

Theorem 11.7 restates Mathlib's `Matrix.det_permute`; Theorem 11.8 is the
framework-specific instance. The 20 three-row minors of the full six-row `S₃`
orbit are all nonzero — checked by exact-integer Python in
[`S3_Trajectory_Verification/`](S3_Trajectory_Verification/), not in Lean.

**Theorem 11.9 — reserved.** (Numbering left open in case a future addition
belongs between 11.8 and 11.10; none exists yet.)

**Theorem 11.10 (Exact on the Product, Reversing on the Sum).** Write the
axial coordinates of the componentwise product and sum of the triadic states
of 2 and 3 (Definition 9.6) as `√2·√3` and `√2+√3`. The Phantom Middle fixes
the first (11.6a) and sends the second to its negation. The product
coordinate is exactly closed (9.7); the sum coordinate falls short of `√5` by
the strictly positive mediator defect `ℰ(2,3) = √2+√3−√5` (9.4).

*Scope.* This is proved for the pair `(2,3)` only, as the Lean file's own
docstring states. The Phantom Middle acts on the sum coordinate `√2+√3`, which
lies in `K`; it does not act on the defect itself, since `√5 ∉ K` (a standard
fact about `K`, not among the Lean results).

Lean: `triadic_product_two_three_eq_sqrt6K` ([L56](Theta__0_Photon/Theta0Photon/Algebra/PhantomTriadicBridge.lean#L56)),
`phantom_middle_preserves_the_triadic_product` ([L76](Theta__0_Photon/Theta0Photon/Algebra/PhantomTriadicBridge.lean#L76)),
`phantom_middle_reverses_the_triadic_sum` ([L86](Theta__0_Photon/Theta0Photon/Algebra/PhantomTriadicBridge.lean#L86))
· [`PhantomTriadicBridge.lean`](Theta__0_Photon/Theta0Photon/Algebra/PhantomTriadicBridge.lean)

> **Interpretation.** Irreducibility of `x²−n` is the ground from which
> every quadratic mediator `√n` enters as a genuinely new element. Two
> independent mediators generate a four-element symmetry group of sign
> flips. Within that group, the Phantom Middle is the *unique* non-trivial
> symmetry that fixes their product (11.6b) — on the pair
> `(2,3)` it acts as the identity on the product coordinate, where the triad
> closes exactly, and as negation on the sum coordinate, where it does not
> (11.10). Since it also negates `√2` and `√3` individually, the negation is not
> specific to the defect; what is specific is that the product of the two
> negated generators is fixed. The Phantom Middle is an automorphism of `K`,
> not of `ℝ` (which has no non-identity field automorphisms; a standard fact,
> not among the Lean results), so the bridge works by restricting the
> real-valued axial coordinates to the countable subfield `K`. `TriadicClosure.lean`'s triadic machinery and
> `GaloisGroup.lean`'s Galois group were built independently, eight months
> apart in the framework's own development but one commit apart in this
> repository's history; §11.10 is the one theorem showing their
> already-independently-verified behaviors agree on the shared coordinate —
> it does not claim either one explains or derives the other. Orientation,
> the sign of a determinant, is the chiral quantity: odd relabellings
> reverse it and even ones preserve it.

## 12. Discrete and Continuum: Operational Orthogonality

*Verification scope. Tier 1, [`SetTheory/Incommensurability.lean`](Theta__0_Photon/Theta0Photon/SetTheory/Incommensurability.lean)
and [`NavierStokes/ContinuumBridge.lean`](Theta__0_Photon/Theta0Photon/NavierStokes/ContinuumBridge.lean).
As that file itself states, these results do not bear on, bound, or resolve
any continuum PDE result, including Navier–Stokes; they are facts about
discrete carriers and their relation to `ℝⁿ`.*

**Definition 12.1 (Operational Orthogonality).** Types `A` and `B` are
operationally orthogonal if `A` is countable and `B` is uncountable.
Lean: `OperationallyOrthogonal`

*Note on "discrete".* In 12.1–12.4 a carrier is "discrete" when it is
countable. In 12.5–12.7 it means a metric space with minimum spacing `h_min>0`.
The two senses are independent: `ℚ(√2)` is countable, yet dense (8.10), so it
has no minimum spacing.

**Theorem 12.2 (No Bridge of Any Kind).** If `A` and `B` are operationally
orthogonal, there is no bijection `A ≃ B`. Consequently, for any notion of
structure-preservation whatsoever, the set of structure-preserving
bijections is empty.
Lean: `isEmpty_equiv_of_operationallyOrthogonal`, `isEmpty_structurePreserving_of_operationallyOrthogonal`

**Theorem 12.3 (Instances).** There is no monotone bijection `ℕ ≃ ℝ`. The
field `ℚ(√2,√3)` is countable, so there is no bijection `ℚ(√2,√3) ≃ ℝ`.
Lean: `isEmpty_monotone_equiv_nat_real`, `isEmpty_equiv_K_real`

**Theorem 12.4 (No Lattice Fills ℝ³).** `ℝ³` is uncountable, so for any
countable lattice and any structure-preservation predicate, there is no
structure-preserving bijection from the lattice onto `ℝ³`.
Lean: `uncountable_euclideanSpace3`, `continuous_fluid_embedding_empty` · [`ContinuumBridge.lean`](Theta__0_Photon/Theta0Photon/NavierStokes/ContinuumBridge.lean)

**Theorem 12.5 (Lattice Gradient Bound).** On a metric space whose distinct
points are at least `h_min>0` apart, any function `u` with `u(x)²≤E`
everywhere satisfies `|u(x)−u(y)|/d(x,y) ≤ 2√E/h_min` for all distinct `x,y`.
Lean: `discrete_lattice_prevents_gradient_blowup`

**Theorem 12.6 (Finitely Many Refinement Levels).** Let `h_N = L₀·(1/√2)ᴺ`.
For `L₀>0` and `h_min>0`, the set of levels `N` with `h_N ≥ h_min` is finite,
and a maximum valid level `N_max` exists.
Lean: `validLevel_finite`, `exists_isMaxValidLevel`

**Theorem 12.7 (Bound at the Finest Level).** The gradient bound of 12.5
holds at `h_{N_max}`, no worse than `2√E/h_min`.
Lean: `gradient_bound_at_max_valid_level`, `gradient_bound_le_of_max_valid_level`

> **Interpretation.** Discrete and continuum are not two views of one
> object: no bijection of any kind connects a countable carrier to `ℝ` or
> `ℝ³`. On the discrete side, a minimum spacing keeps difference quotients
> bounded, and refinement by the diagonal factor `1/√2` terminates after
> finitely many levels. Four families of results in this paper —
> arithmetic descent (§5, §7, Lemma 8.3), order-theoretic retraction failure
> (§8), field-theoretic non-membership (§11), and cardinality (§12) — are the
> same phenomenon recurring at four different levels of mathematical
> machinery, not a single ladder of increasing strength; each is a fact of
> its own genre, checked on its own terms.

## 13. Synthesis

The formalization establishes the following. A node's self-relation `x ℛ x`
is dominated by every reflexive relation, is preserved under any relabelling
of nodes, and is unchanged by adding a metric, order or operation
(Sections 2–3). Primality is exactly the condition `Div(p) = {1,p}` (§4).

The horizontal and diagonal measures of the unit square are incommensurable,
with positive gap `2−√2`, while the boundary itself unfolds isometrically
(§5). `(ℝ,+)` and `U(1)` are non-isomorphic even as abstract groups, and `2π`
shares no integer measure with the unit step (§6). The phase-drift angle is a
well-defined, non-vacuous predicate, and a fixed-step Axial clock never
closes the diagonal gap (§7).

A number system containing `√2` admits no order-preserving retraction onto
`ℚ`, and `ℚ(√2)` itself is a kernel-checked ordered field in which the
rationals are dense (§8). The triadic state satisfies the geometric-mean
bridge, strictly positive mediator defect, and 45° equipartition (§9), and
discrete intervals carry a symmetric harmonic center (§10).

The algebraic ground holds in full: `x²−n` is irreducible for every
non-square `n`, every `ℚ(√n)` has degree 2, and `ℚ(√2,√3)` has degree 4 with
a Klein four symmetry whose composite flip is the Phantom Middle; determinants
of triadic matrices carry a chiral sign (§11). The triad is exactly closed
under multiplication, and classical `ℕ` is its projection, discarding
precisely the mediator defect (§9) — **and, for the pair `(2,3)`, the Phantom Middle respects that same split:
it fixes the product coordinate and reverses the sum coordinate (§11.10).**
Discrete and continuum admit no bijection of any kind, while the discrete
side carries bounded gradients and finitely many refinement levels (§12).

## Appendix A: Reproducing the Verification

**Tier 1** (from the repository root; `elan` installs the pinned toolchain automatically):
```sh
git clone https://github.com/MosesDSI/primitive-reflexivity-lean4.git
cd primitive-reflexivity-lean4
lake exe cache get
lake build
lake build PrimitiveReflexivity.AxiomCheck
```
A clean exit with `Build completed successfully` is the verification; the
`AxiomCheck` build prints the axiom footprint of each `Foundations` theorem.

**Tier 2** (each file individually, with the same `v4.33.1` toolchain):
```sh
lean R3_bare_lean/<file>.lean
lean Section_VI_Incommensurability/<file>.lean
```
See `R3_Lean_Testing_Reproduction_Guide.md` for expected output per file.

**Companion project (Tier 1),** from the repository root:
```sh
cd Theta__0_Photon
lake exe cache get
lake build
```

## Appendix B: Index of Results

| Result | Lean declaration | File | Tier |
|---|---|---|---|
| 2.3 | `reflexive_minimality` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 2.4 | `reflexive_isomorphism` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 3.1 | `metric_independence` | [`R3_metric.lean`](R3_bare_lean/R3_metric.lean) | 2 |
| 3.2 | `a_metric_independence_order` | [`R3_order.lean`](R3_bare_lean/R3_order.lean) | 2 |
| 3.3 | `a_metric_independence_algebraic` | [`R3_algebraic.lean`](R3_bare_lean/R3_algebraic.lean) | 2 |
| 3.4 | `a_metric_independence_v2` | [`R3_decorated.lean`](R3_bare_lean/R3_decorated.lean) | 2 |
| 2.5, 3.5–3.6 | `Node`, `R`, `zero_is_not_a_coordinate`, `off_diagonal_dist_ne_zero`, `dist_eq_zero_iff_R` | [`Basic.lean`](Theta__0_Photon/Theta0Photon/Basic.lean), [`Main.lean`](Theta__0_Photon/Main.lean) | 1 |
| 4.3 | `prime_incompressibility` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 5.2 | `manhattan_is_rational` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 5.3 | `diagonal_is_irrational` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 5.4 | `no_common_rational_measure` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 5.5 | `delta_gap_pos` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 5.10–5.13 | `square_diagonals_orthogonal`, `d2_in_centered_subspace`, `sample_decomp_two`, `two_cell_direct_sum`, `sample_space_direct_sum`, `finrank_centeredSubspace` | [`CenteredKernel.lean`](Theta__0_Photon/Theta0Photon/Statistics/CenteredKernel.lean) | 1 |
| 5.6–5.9 | `unfold_bounds`, `unfold_isometry_same_edge`, `unfold_corner_adjacency`, `perimeter_unfold_conservation` | [`SquareUnfolding.lean`](PrimitiveReflexivity/Geometry/SquareUnfolding.lean) | 1 |
| 6.1 | `group_inequivalence` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 6.2 | `real_not_equiv_circle` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 6.3 | `two_pi_irrational` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 6.4 | `period_incommensurability` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 7.3 | `PhaseDriftMatch` | [`Section_VI_dual_clock.lean`](R3_bare_lean/Section_VI_dual_clock.lean) | 2 |
| 7.4 | `polar_axial_incommensurable` | [`Polar_Axial_Incommensurability.lean`](Section_VI_Incommensurability/Polar_Axial_Incommensurability.lean) | 2 |
| 7.5–7.6 | `const_step_reaches`, `axial_clock_never_closes_the_diagonal_gap` | [`Axial_Divergence_Theorem.lean`](Section_VI_Incommensurability/Axial_Divergence_Theorem.lean) | 2 |
| 8.1–8.6 | `retraction_is_identity`, `no_retraction_if_gap`, `rat_no_sqrt_two`, `no_order_retraction_rat`, `no_retraction_local`, `density_needed`, `retract_needed`, `mono_needed` | [`OrderObstruction.lean`](PrimitiveReflexivity/Discrete/OrderObstruction.lean) | 1 |
| 8.7–8.11 | `s_mul_s`, field laws, `trichotomy`, `transitivity`, `pos_add`, `mul_pos`, `qs_dense`, `incommensurability_blocks_retraction` | [`OrderObstruction.lean`](PrimitiveReflexivity/Discrete/OrderObstruction.lean) | 1 |
| 9.2 | `geometric_mean_bridge` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 9.4 | `mediator_defect_positive` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 9.5 | `equipartition_fixed_point` | [`Foundations.lean`](PrimitiveReflexivity/Foundations.lean) | 1 |
| 9.6–9.11 | `TriadicNat`, `triadic_multiplication_closed`, `triadic_addition_not_closed`, `π`, `projection_commutes_on_n`, `correction_identity` | [`TriadicClosure.lean`](Theta__0_Photon/Theta0Photon/Algebra/TriadicClosure.lean) | 1 |
| 9.12 | `const_one_satisfies_both_conditions` | [`UniquenessTest.lean`](Theta__0_Photon/Theta0Photon/Algebra/UniquenessTest.lean) | 1 |
| 10.2–10.4 | `harmonic_distance_symmetry`, `harmonic_center_in_C2`, `tri_partition_distance_sums` | [`HarmonicCenter.lean`](PrimitiveReflexivity/Discrete/HarmonicCenter.lean) | 1 |
| 11.1 | `triadic_no_rational_root`, `triadic_ground_irreducible` | [`GroundAxiom.lean`](Theta__0_Photon/Theta0Photon/Algebra/GroundAxiom.lean) | 1 |
| 11.2–11.4 | `sqrt_finrank`, `sqrt2_field_eq`, `sqrt3_notMem`, `sqrt2_sqrt3_finrank` | [`FieldTower.lean`](Theta__0_Photon/Theta0Photon/Algebra/FieldTower.lean) | 1 |
| 11.5 | `card_Gal_eq_four`, `IsGalois`, `IsKleinFour` | [`GaloisGroup.lean`](Theta__0_Photon/Theta0Photon/Algebra/GaloisGroup.lean) | 1 |
| 11.6 | `phantom_middle`, `phantom_middle_sqrt2`, `galoisKleinFourEquiv_phantom_middle` (a); `phantom_middle_fixes_sqrt6K`, `sigma_negates_sqrt6K`, `tau_negates_sqrt6K`, `stabilizer_sqrt6K`, `phantom_middle_fixed_iff`, `fixedField_phantom_middle` (b–d) | [`GaloisGroup.lean`](Theta__0_Photon/Theta0Photon/Algebra/GaloisGroup.lean), [`PhantomFixedField.lean`](Theta__0_Photon/Theta0Photon/Algebra/PhantomFixedField.lean) | 1 |
| 11.7–11.8 | `chiral_sign_law`, `transposition_flips_orientation`, `fin3_isOdd_iff_isSwap`, `canonicalOrbitMatrix_det` | [`ChiralSign.lean`](Theta__0_Photon/Theta0Photon/Geometry/ChiralSign.lean) | 1 |
| 11.10 | `triadic_product_two_three_eq_sqrt6K`, `phantom_middle_preserves_the_triadic_product`, `phantom_middle_reverses_the_triadic_sum` | [`PhantomTriadicBridge.lean`](Theta__0_Photon/Theta0Photon/Algebra/PhantomTriadicBridge.lean) | 1 |
| 12.1–12.3 | `OperationallyOrthogonal`, `isEmpty_structurePreserving_of_operationallyOrthogonal`, `isEmpty_monotone_equiv_nat_real`, `isEmpty_equiv_K_real` | [`Incommensurability.lean`](Theta__0_Photon/Theta0Photon/SetTheory/Incommensurability.lean) | 1 |
| 12.4–12.7 | `continuous_fluid_embedding_empty`, `discrete_lattice_prevents_gradient_blowup`, `validLevel_finite`, `exists_isMaxValidLevel`, `gradient_bound_at_max_valid_level` | [`ContinuumBridge.lean`](Theta__0_Photon/Theta0Photon/NavierStokes/ContinuumBridge.lean) | 1 |
