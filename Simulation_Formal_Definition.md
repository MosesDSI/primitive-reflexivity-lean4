# Simulation: A Formal Definition

### Primitive Reflexivity framework, following the two-clock proposition

This definition fits the formal setup of the two-clock proposition. It makes
"simulation" precise rather than speculative, and every condition in it can be
checked.

## Definition in one sentence

> A simulation is a faithful, step-by-step rendering of a discrete carrier
> into a phase space that the carrier fills densely but can never realize.

## Formal definition

A simulation consists of five components `(Λ, s, Φ, F, ρ)`, in three groups:

**A carrier `Λ` with a step map `s : Λ → Λ`.** This is the realized, discrete
part, countable by assumption. For the trap:

`Λ = ℕ`,  `s(n) = n + 1`

**A phase space `Φ` with its own dynamics `F : Φ → Φ`.** For the trap, `Φ` is
the torus `𝕋²` (the unit square with opposite edges identified), and `F`
advances both phases:

`F(θ₁, θ₂) = (θ₁ + √30, θ₂ + √33) mod 1`

**A rendering map `ρ : Λ → Φ`.** For the trap:

`ρ(n) = (n√30 mod 1, n√33 mod 1)`

It must satisfy four conditions.

**(S1) Equivariance.** The rendering follows the carrier tick by tick:

`ρ(s(n)) = F(ρ(n))` for all `n ∈ Λ`

Advancing the carrier and then rendering gives the same result as rendering
and then advancing in phase space. This is what makes it a simulation of
*this* carrier rather than an arbitrary picture. In computer science, this is
the functional case of Milner's simulation relation: every step of one system
is matched by a step of the other.

**(S2) Faithfulness.** `ρ` is injective: distinct carrier states never render
to the same point.

`ρ(n) = ρ(m) ⟹ n = m`

For the trap, this follows from the irrationality of `√30` alone: if
`ρ(n) = ρ(m)` with `n ≠ m`, then `(n − m)√30` would be an integer.

**(S3) Density.** The rendered states come arbitrarily close to every point of
`Φ`:

for every `θ ∈ Φ` and every `ε > 0`, there is `n ∈ Λ` with `dist(ρ(n), θ) < ε`

For the trap, this is Kronecker's theorem, since `1`, `√30` and `√33` are
linearly independent over `ℚ`.

**(S4) Non-realization.** There is no bijection between `Λ` and `Φ`:

`Λ` countable, `Φ` uncountable `⟹` no bijection `Λ ≃ Φ`

This is the verified operational-orthogonality theorem (§12 of the Verified
Edition). The rendered states `ρ(Λ)` therefore form a proper, countable part
of `Φ` that never fills it.

### A consequence that captures "rendered"

From (S3) and the compactness of `Φ`: for every resolution `h > 0` there is a
finite number of ticks `N` such that the first `N` rendered states come within
`h` of every point of `Φ`.

for every `h > 0`, there is `N` with: for every `θ ∈ Φ`, some `n ≤ N` has
`dist(ρ(n), θ) < h`

At any finite resolution, a simulation is indistinguishable from its phase
space after finitely many ticks, yet it never becomes the phase space.

In discrete-first terms, the continuum is what a simulation looks like at
finite resolution. This is also where the PDE world sits in the framework:
PDEs are statements about `Φ`, and a result like the Lax equivalence theorem
says when a discrete carrier's rendering converges to them.

### Where the Phantom Middle fits

The mediator is not part of the simulation's states. It belongs to the
symmetry group `G` acting on `Φ`, as in Proposition (P4). What the simulation
conserves under the mediator are the quantities `G` leaves fixed. For
`ℚ(√2, √3)`, the verified theorem `stabilizer_sqrt6K` pins this down: the
Phantom Middle is the unique non-identity symmetry preserving the product of
the two generators,

`π(√2 · √3) = √2 · √3`,  `σ(√2 · √3) = τ(√2 · √3) = −√2 · √3`

### Contrast with everyday usage

"Simulation" here does not mean fake, and it does not mean a computer
program. It means that the carrier and the phase space play different formal
roles:

- The carrier runs: it is discrete, countable and realized.
- The phase space displays: it is uncountable and never realized.
- The simulation is the structure-preserving map between them.

## Verification status for the trap

| Condition | Status | Lean |
|---|---|---|
| (S1) | True by construction | Quick target |
| (S2) | **Verified**, both tiers. Bare Lean, no Mathlib: `SimulationExchange.faithful` proves faithfulness for `s·s = d`, any non-square `d`, in any characteristic-0 commutative ring. Mathlib tree: `Theta0Photon.SimulationExchangeBridge.faithful_real` and `.fract_faithful` instantiate it at `R = ℝ`, `s = √d` (any non-square `d`, not just the trap's `d = 30`), stated directly with `Int.fract`. | Carried out in both `SimulationExchange/` (bare Lean) and `Theta__0_Photon/Theta0Photon/Algebra/SimulationExchangeBridge.lean` (Mathlib bridge) |
| (S3) | Standard theorem (Kronecker), not yet formalized | Substantial target |
| (S4) | Follows from the verified operational-orthogonality theorem once `Φ` is shown uncountable (a short lemma) | Quick target |

See [`Foundations_of_Primitive_Reflexivity_Verified_Edition.md`](Foundations_of_Primitive_Reflexivity_Verified_Edition.md)
for the verified theorems this definition builds on, and
[`Instructure_Formal_Definition.md`](Instructure_Formal_Definition.md) for the
companion definition of the finite datum that generates a family of
simulations, one per orientation.
