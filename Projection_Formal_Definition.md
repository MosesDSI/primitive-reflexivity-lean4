# Projection: A Formal Definition

### Primitive Reflexivity framework, companion to "Simulation" and "Instructure"

This document defines *projection* precisely and places it between
*simulation* and *experience*. The informal idea is a reading that keeps part
of a structure and lets the rest go. The formal version below requires that
the reading be exact on what it keeps, exactly accountable for what it lets
go, and impossible to undo. The framework already contains one verified
projection, the classical count of the triadic state (§9 of the Verified
Edition). This definition states in general what that example has.

## Definition in one sentence

> A **projection** is a map from a richer structure to a coarser one that is
> exact on what it keeps, exactly accountable for what it discards, cannot be
> undone, and, when its target is finite, is decided by finitely many integer
> comparisons with no boundary case.

## Etymology

*Projection* comes from Latin *proicere*, "to throw forth", from *pro-*
("forward") and *iacere* ("to throw"). Both senses are intended. A
projection throws a structure *forward* onto a surface that has less room than
the structure, as a shadow or a map does. Within this framework, the
*forward* direction is that of the carrier, the one direction that only goes
one way: what is thrown forward cannot be thrown back (P3).

## Formal definition

A projection consists of five components `(X, ⊙, Y, ⊕, p)`, in three groups.

**A source `X` with an operation `⊙`.** This is the richer description. For
the classical projection it is the typed triadic numbers `TriadicNat`, each
`(n, polar, axial, boundary)` with `polar = n`, `axial = √n`,
`boundary = n²`, and `⊙` is componentwise addition.

**A target `Y` with an operation `⊕`.** This is the coarser description.
For the classical projection, `Y = ℕ` with ordinary `+`.

**A projection map `p : X → Y`.** For the classical projection,

`π(n, polar, axial, boundary) = n`

(The Verified Edition also writes `π` for the Phantom Middle. In this
document, `π` is always the classical projection, and the Phantom Middle is
named in words.)

It must satisfy four conditions.

**(P1) Exact on what it keeps.** The projection carries the source operation
to the target operation:

`p(x ⊙ y) = p(x) ⊕ p(y)`

For the classical projection this is `projection_commutes_on_n`. It holds by
`rfl`, because componentwise addition adds the counts by definition. That is
the point: the kept coordinate is exactly the one on which the two
operations agree.

**(P2) Exactly accountable residue.** There is an explicit residue
`r(x, y)` that measures what `p` discards: the source result, corrected by
`r`, is what a genuine source element over `p(x) ⊕ p(y)` would carry. For the
classical projection, the residue is the mediator defect
`ℰ(n, m) = √n + √m − √(n + m)`:

`(x ⊙ y).axial − ℰ(n, m) = √(π(x) + π(y))`

This is `correction_identity`. The residue is not an error term to be
estimated. It is a closed formula, and for `n, m > 0` it is strictly
positive (`mediator_defect_positive`), so the projection is never lossless on
sums.

**(P3) Irreversibility.** No structure-preserving map back from `Y` recovers
what `p` discarded. Two forms appear in the framework.

- *Fibre form.* Distinct source descriptions share a projection. The
  componentwise sum `x ⊙ y` and the genuine triad for `n + m` have the same
  count, but different axial coordinates (`triadic_addition_not_closed`). A
  map from counts back to triads must pick one and lose the other.
- *Order form.* Once a structure contains a point incommensurable with its
  target, no order-preserving map back onto the target restricts to the
  identity on it: there is no monotone `f : ℚ(√2) → ℚ` with `f(q) = q` for
  every rational `q` (`incommensurability_blocks_retraction`, Theorem 8.11).

**(P4) Exact readout.** When `Y` is finite, `p` is decided by finitely many
integer comparisons from the data that define the source, and no source
element produced by the dynamics lies on a boundary between two values of
`p`. The verified instance is the **side bit** of a walker (next section):
whether `frac(n√d)` is above or below `½` is the parity of the integer `a`
with `a² ≤ 4n²d < (a+1)²` (`FloorPos`), and the walker is never on the wall
(`wall_never_hit`, `fixed_points_never_occupied`).

## Three verified projections

| Projection | Keeps (P1) | Discards, exactly (P2) | Irreversible (P3) | Readout (P4) |
|---|---|---|---|---|
| Classical count `π : TriadicNat → ℕ` | `projection_commutes_on_n` | Mediator defect: `correction_identity`, `mediator_defect_positive` | Fibre form: `triadic_addition_not_closed` | Not applicable: `Y = ℕ` is infinite |
| Diagonal split of a pair `s = (s₁, s₂)` onto the shared diagonal `D1` | Shared mean, which is additive in the pair (standard; not separately formalized) | The deviation along `D2`, exactly: `s = mean·D1 + deviation` (`sample_decomp_two`) | Fibre form: pairs with equal mean and different deviation | Not applicable |
| Side bit of a walker, `Φ = 𝕋 → {below, above}` at the `½` wall | Which side of the wall | The position within the side | Fibre form: uncountably many phases share each bit | `FloorPos`, `wall_never_hit`, `fixed_points_never_occupied` |

The diagonal split is the projection that §8 of *Discrete Evidence in
Neuroscience* reads as experienced depth: the shared diagonal `D1` is the
fused view and the discarded `D2` is depth. In that reading, depth is the
residue of a projection, recovered by comparing two projections (two eyes,
or two ticks), not by inverting one.

## Projection and symmetry

A projection is orientation-free when its value is fixed by the symmetry
group. The rows of the Galois ladder in the Instructure definition are the
targets of such projections. For a subgroup `H` of `G_I`, averaging over `H`,
`x ↦ (1/|H|) Σ_{h ∈ H} h(x)`, is a projection of `K_I` onto the field `H`
fixes: it is ℚ-linear (P1), its residue `x − avg_H(x)` is explicit (P2), and
it sends distinct elements to the same value (P3). Averaging over all of
`G_I` lands in `ℚ`, where the instructure's integers live. Averaging over the
two-element subgroup generated by the Phantom Middle lands in `ℚ(√(d₁d₂))`, the field that
`fixedField_phantom_middle` identifies. The fixed fields are verified; the
averaging map is standard and not formalized.

The side bit is *not* orientation-free. A single sign flip inverts it at
every tick (`flip_inverts_side`). The **in-step bit** (whether the two walkers
are on the same side of their walls) is a projection that the Phantom Middle
fixes and each single flip inverts, at every tick
(`phantom_middle_preserves_inStep`). It is the bit-level shadow of the
mediator row of the Galois ladder.

## Relation to simulation

> **Proposition.** A simulation's rendering and a projection point in opposite
> directions. The rendering `ρ : Λ → Φ` is faithful (S2): it embeds a
> countable carrier into an uncountable phase space and forgets nothing. A
> projection `p : Φ → Y` forgets. Their composite `p ∘ ρ : Λ → Y` is faithful
> only if `Y` is infinite; when `Y` is finite it is never faithful, because
> infinitely many ticks share finitely many values.

*Proof.* If `Y` is finite and `Λ = ℕ`, the map `p ∘ ρ` sends infinitely
many ticks into finitely many values, so two ticks share a value
(pigeonhole). ∎

In one line: **a simulation renders a carrier into more than it is; a
projection reads a rendering into less than it is.** The composite of the two
is the subject of the companion definition
[`Experience_Formal_Definition.md`](Experience_Formal_Definition.md).

## Contrast with everyday usage

"Projection" here does not mean the psychological sense of attributing one's
own states to others, and it does not mean only the linear-algebra sense of
an idempotent map. A linear projection `P` with `P² = P` satisfies (P1) for
addition and has an exact residue `x − Px` (P2), so it is an instance. The
definition here asks for more than idempotence: the residue must be named
and computed, and irreversibility must be proved rather than assumed.

## Verification status

| Component | Status |
|---|---|
| (P1) for the classical count | **Verified**, Mathlib tier: `projection_commutes_on_n` (`Theta__0_Photon/Theta0Photon/Algebra/TriadicClosure.lean`) |
| (P2) residue is exactly the mediator defect, and positive | **Verified**, Mathlib tier: `correction_identity`, `mediator_defect_positive` (also in `PrimitiveReflexivity/Foundations.lean`) |
| (P3) fibre form for the classical count | **Verified**, Mathlib tier: `triadic_addition_not_closed` |
| (P3) order form, `ℚ(√2) → ℚ` | **Verified**, bare Lean: `incommensurability_blocks_retraction` (`PrimitiveReflexivity/Discrete/OrderObstruction.lean`) |
| (P4) side bit decided in integers, never on the wall | **Verified**, bare Lean: `FloorPos`, `wall_never_hit`, `fixed_points_never_occupied` (`SimulationExchange/SimulationExchange/Boundary.lean`) |
| Diagonal split: exact residue (P2) | **Verified**, Mathlib tier: `sample_decomp_two` (`Theta0Photon/Statistics/CenteredKernel.lean`). Additivity of the mean (P1) is standard and not separately formalized |
| Side bit inverted by a flip; in-step bit fixed by the Phantom Middle | **Verified**, bare Lean: `flip_inverts_side`, `phantom_middle_preserves_inStep` |
| The four conditions as one abstract structure, with the three instances proved to satisfy it | Not formalized. A quick target: a bare-Lean `structure Projection` and three instances |
| The proposition: `p ∘ ρ` is not faithful when `Y` is finite | Proved by hand (pigeonhole). A quick target |

See [`Simulation_Formal_Definition.md`](Simulation_Formal_Definition.md) for
the rendering a projection reads,
[`Instructure_Formal_Definition.md`](Instructure_Formal_Definition.md) for the
finite datum the rendering is executed from, and
[`Experience_Formal_Definition.md`](Experience_Formal_Definition.md) for the
tick-by-tick record a projection of a simulation makes.
