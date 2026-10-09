# Instructure: A Formal Definition

### Primitive Reflexivity framework, companion to "Simulation: A Formal Definition"

This document defines *instructure* precisely and relates it to *simulation*.
The informal idea is a structure that contains, within itself, the
instruction for its own use. The formal version below identifies that
structure as finite integer data whose self-relations are a complete building
rule, and shows that executing it produces a family of simulations, one for
each choice of orientation.

## Definition in one sentence

> An **instructure** is a finite, orientation-free datum whose self-relations
> are the complete rule for building an exact arithmetic, its symmetries, and
> a family of simulations, one for each choice of orientation, with every
> question those simulations raise decidable from the datum alone.

## Etymology

*Instructure* combines *structure* (Latin *structura*, from *struere*, "to
heap up, arrange, build") and *instruct* (Latin *instruere*, "to build in,
equip, arrange"). Both come from *struere*. The prefix carries two readings,
both intended: the instruction is *in* the structure (embedded, not supplied
from outside), and the structure *builds in* (it is the equipment for what is
built from it).

## Formal definition

### The datum

An **instructure** is a finite tuple of positive integers

`I = (d₁, …, dₖ)`

satisfying the **independence condition**: for every nonempty set of indices
`S ⊆ {1, …, k}`, the product `∏ᵢ∈S dᵢ` is not a perfect square. Each `dᵢ` is
read as the self-relation of a generator `xᵢ`:

`xᵢ · xᵢ = dᵢ`

This rule, one line per generator, is the entire instruction.

### Execution

A single fixed procedure `E`, the same for every instructure, executes `I` in
three stages.

**(E1) Arithmetic.** Build the ring of polynomials in `x₁, …, xₖ` with
rational coefficients, and rewrite every `xᵢ²` as `dᵢ`:

`K_I = ℚ[x₁, …, xₖ] / (x₁² − d₁, …, xₖ² − dₖ)`

Under the independence condition this is a field of degree `2ᵏ` over `ℚ`, the
multiquadratic field `ℚ(√d₁, …, √dₖ)`. Its elements are rational combinations
of the `2ᵏ` products of distinct generators.

**(E2) Symmetry.** The rule `xᵢ² = dᵢ` cannot tell `xᵢ` from `−xᵢ`. Flipping
the sign of any subset of generators preserves all of the arithmetic, giving
the symmetry group

`G_I = Gal(K_I / ℚ) ≅ (ℤ/2)ᵏ`

**(E3) Simulations.** An orientation `ι` is a choice of sign for each
generator, that is, one of the `2ᵏ` embeddings `ι : K_I → ℝ`. Each orientation
determines a simulation `S_{I,ι}` in the sense of the companion definition
(see [`Simulation_Formal_Definition.md`](Simulation_Formal_Definition.md)):

`Λ = ℕ`,  `Φ = 𝕋ᵏ`,  `ρι(n) = (n · ι(x₁) mod 1, …, n · ι(xₖ) mod 1)`

with the carrier step `n ↦ n + 1` and phase dynamics `F_ι` advancing
coordinate `i` by `ι(xᵢ)`.

### The five conditions

An instructure, together with its execution, satisfies the following.

**(N1) Finite and orientation-free.** `I` is finitely many integers, and
every symmetry in `G_I` fixes it. The instruction contains no handedness: it
is the part every orientation shares.

**(N2) Generic execution.** `E` depends on nothing but `I`: the rewrite rule,
iteration of the step, and integer arithmetic. Like a screwdriver, the
executor contributes operation, not outcome.

**(N3) Determination up to symmetry.** `I` determines `K_I`, `G_I`, and the
full family of `2ᵏ` simulations. `G_I` permutes the family: for each symmetry
`g`, the simulation for orientation `ι ∘ g` is the simulation for `ι` with the
flipped coordinates reflected, `θᵢ ↦ −θᵢ`.

`ρ_{ι∘g}(n) = R_g(ρι(n))`

**(N4) Exact decidability.** Every order question in every `S_{I,ι}` (is this
value above that wall, which side of the midpoint) is settled by finitely
many integer computations from `I` alone. The certified bounds use integer
square roots of `dᵢ · D²` and tighten until the answer is forced; they always
terminate, because a nonzero element of `K_I` never takes the value `0`.

**(N5) Non-degeneracy.** Because no `dᵢ` is a square, each rotation `ι(xᵢ)` is
irrational, so every rendering is faithful (simulation condition S2). Because
of the full independence condition, `1, ι(x₁), …, ι(xₖ)` are linearly
independent over `ℚ`, so every rendering is dense (S3, by Kronecker's
theorem).

## Relation to simulation

> **Proposition.** Every instructure with `k` generators executes to a family
> of `2ᵏ` simulations, one per orientation, each satisfying the four
> simulation conditions (S1)–(S4). The symmetry group permutes the family
> transitively, and the instructure is exactly the data the whole family
> shares.

*Proof outline.* (S1) holds by construction, since `ρι(n + 1) = Fι(ρι(n))`.
(S2) and (S3) follow from (N5). (S4) holds because `ℕ` is countable and `𝕋ᵏ`
is uncountable, by the operational-orthogonality theorem (§12 of the Verified
Edition). Transitivity is the standard correspondence between the embeddings
of a Galois extension and its Galois group.

In one line: **an instructure is to a simulation what a blueprint is to a
building seen from one side.** The instructure is finite, exact and
orientation-free. A simulation needs an orientation, runs on the carrier and
displays in phase space. The same instructure yields all the mirror-image
simulations.

## The Galois ladder: instructure, mediator, simulation

For two generators, the three roles sit at three levels of the Galois
correspondence. The more symmetry a quantity survives, the less it depends on
orientation.

| Role | Fixed by | Lives in | Orientation-dependent? |
|---|---|---|---|
| Instructure | All of `G_I` | `ℚ` (the integers `d₁, d₂`) | No |
| Mediator (Phantom Middle `π`) | The subgroup `⟨π⟩` | `ℚ(√(d₁d₂))` | Partly: blind to flipping both |
| Simulation | Only the identity | `K_I`, rendered through `ι` | Yes |

The middle row is now verified for **every** independent pair `(d₁, d₂)` by
`GeneralPhantomFixedField.fixedField_phantom_middle` and `stabilizer_sqrt_prod`:
the Phantom Middle fixes exactly `ℚ(√d₁·√d₂)`, and it is the unique
non-identity symmetry preserving `√d₁ · √d₂`. The `(2,3)` instance —
`fixedField_phantom_middle` and `stabilizer_sqrt6K` fixing exactly `ℚ(√6)` —
is recovered as a sanity check of the general theorem, not reproved
separately.

## Oriented instructures and the screw

Handedness is not part of the instructure itself; it enters with the
orientation. When the handedness is built into the object, as in a screw
thread, the relevant notion is an **oriented instructure**, the pair `(I, ι)`.
In the screw analogy:

- the unoriented instructure `I` is the blueprint that can produce either a
  left-handed or a right-handed thread;
- the oriented instructure `(I, ι)` is a particular thread, whose handedness
  is fixed;
- the screwdriver is the generic executor `E`, which turns either way and
  contributes only rotation.

## Worked example: the `√30` / `√33` trap

The trap's instructure is `I = (30, 33)`. The independence condition holds:
30 and 33 are non-squares, and `30 · 33 = 990 = 3² · 110` is not a square.

- **Arithmetic (E1):** `K_I = ℚ(√30, √33)` has degree 4, with basis
  `1, √30, √33, √110`, since `√30 · √33 = 3√110`.
- **Symmetry (E2):** `G_I` is the Klein four-group. The Phantom Middle flips
  both generators and fixes `ℚ(√110)`.
- **Simulation (E3):** the chosen orientation takes both roots positive and
  renders `ρ(n) = (n√30 mod 1, n√33 mod 1)` on the torus.
- **Exact decidability (N4):** the published trap decides every wall and
  midpoint question from integer square roots of `30D²`, `33D²` and `110D²`.
  In the test runs, 20 digits always sufficed.

Every exact decision the trap makes is executed from the two integers 30 and
33. The continuous-looking square of phases is its rendering.

## Reflexive reading

> **Interpretation.** Each generator's instruction is its relation to
> itself: `xᵢ · xᵢ = dᵢ`. Multiplying the generator by itself returns the
> datum, and nothing outside the generator is referenced. This parallels the
> primitive self-relation `x ℛ x`: the instructure is built from
> self-relations alone, and everything else — the arithmetic, the symmetries
> and the simulations — is executed from them. The verified ground axiom
> (`x² − n` irreducible for non-square `n`) guarantees each generator is
> individually genuinely new, not reducible to a rational — one line of the
> independence condition. The full independence condition (no subset product
> a perfect square), which the degree-`2ᵏ` field and Klein-ladder claims
> below actually rest on, is the separate, stronger condition recorded in the
> verification-status table.

## Verification status

| Component | Status |
|---|---|
| Non-square `d` makes `x² − d` irreducible (N5) | Verified for every non-square `d`: `triadic_ground_irreducible` |
| Each `ℚ(√d)` has degree 2 | Verified for every non-square `d`: `sqrt_finrank` |
| Degree 4 and Klein four symmetry for `k = 2` | Verified for **every** independent pair: `GeneralFieldTower.sqrt_sqrt_finrank`, `GeneralGaloisGroup.card_Gal_eq_four`, `isGalois_K`, `isKleinFour_K` (`(2,3)` instance recovered as a sanity check: `sqrt2_sqrt3_finrank`, `card_Gal_eq_four`, `IsKleinFour`) |
| Mediator's fixed field is `ℚ(√(d₁d₂))` | Verified for **every** independent pair: `GeneralPhantomFixedField.fixedField_phantom_middle`, `stabilizer_sqrt_prod` (`(2,3)` instance recovered as a sanity check: `fixedField_phantom_middle`, `stabilizer_sqrt6K`) |
| Triadic product/sum split vs. the Phantom Middle (§11.10 of the Verified Edition) | Verified for **every** independent pair: `GeneralPhantomTriadicBridge.phantom_middle_preserves_the_triadic_product`, `phantom_middle_reverses_the_triadic_sum` (`(2,3)` instance recovered as a sanity check) |
| (S4) non-realization | Verified abstractly: operational orthogonality; needs `𝕋ᵏ` uncountable |
| Degree `2ᵏ` and `(ℤ/2)ᵏ` for general `k > 2` | Standard; not formalized. (`k = 2`, i.e. any independent *pair*, is fully verified — see the rows above; this row is specifically about three or more generators.) |
| Transitive action on orientations (N3) | Standard; not formalized |
| Density (S3) via Kronecker | Standard; not formalized |
| Exact decidability procedure (N4) | Implemented and tested in the trap (JavaScript); not formalized in Lean |

The two-generator Galois ladder — field tower, Galois group, Phantom Middle's
fixed field, and its interaction with the triadic product/sum split — is now
verified in Lean for every independent pair `(d₁,d₂)`, not just `(2,3)`; see
`ROADMAP_LEDGER.md` for the four-step development history. The natural next
Lean steps from here are: generalizing degree `2ᵏ`/`(ℤ/2)ᵏ` from `k = 2` to
arbitrary `k` (a genuinely new induction, not a reparametrization); Kronecker
density (S3); and formalizing the trap's exact-decidability procedure (N4),
currently only implemented and tested outside Lean.

See [`Foundations_of_Primitive_Reflexivity_Verified_Edition.md`](Foundations_of_Primitive_Reflexivity_Verified_Edition.md)
for the verified theorems this definition builds on, and
[`Simulation_Formal_Definition.md`](Simulation_Formal_Definition.md) for the
companion definition of the rendering a given orientation produces.
