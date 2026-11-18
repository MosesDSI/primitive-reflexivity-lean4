# Experience: A Formal Definition

### Primitive Reflexivity framework, companion to "Simulation", "Instructure" and "Projection"

This document defines *experience* precisely, as the last of four linked
roles. An instructure is executed into a family of simulations. A simulation
renders a carrier into a phase space. A projection reads a rendering into
something coarser. An **experience** is what an observer's projection of a
simulation records, one tick at a time.

The definition is structural. It says what kind of object an experience is
and which conditions it satisfies, and every condition can be checked. It
does not claim that human or animal experience is such an object. That claim
is the hypothesis of *Discrete Evidence in Neuroscience* (§2, §8), and it is
marked there as interpretive. This document supplies the formal object that
hypothesis refers to.

## Definition in one sentence

> An **experience** is the tick-by-tick record that an observer's
> finite-resolution projection makes of a simulation: discrete and finite at
> every tick, accumulated only forward along the carrier, decided exactly
> from integers, and never eventually periodic, although no single reading
> is ever new.

## Etymology

*Experience* comes from Latin *experientia*, from *experiri*, "to try, to
test", built on the same root as *peritus* ("skilled, tried") and *periculum*
("a trial"). An experience is a record of trials: at each tick the observer
asks one finite question of the rendering (which side? in step or not?) and
registers the answer. Nothing is registered without a question being asked,
and the observer chooses the question (X5).

## Formal definition

An experience consists of a simulation, an observer, and the record the
observer makes of the simulation.

**A simulation `S = (Λ, s, Φ, F, ρ)`** in the sense of
[`Simulation_Formal_Definition.md`](Simulation_Formal_Definition.md). For the
trap, `Λ = ℕ`, `Φ = 𝕋²` and `ρ(n) = (n√30 mod 1, n√33 mod 1)`.

**An observer `O = (Y, p)`**: a finite set `Y` of readings and a projection
`p : Φ → Y` in the sense of
[`Projection_Formal_Definition.md`](Projection_Formal_Definition.md). The
cells `p⁻¹(y)` partition `Φ`. The size of the cells is the observer's
**resolution**, the window `ε` of *Discrete Evidence in Neuroscience* §2.

**The record `e = p ∘ ρ : Λ → Y`**, read along the carrier:

`e(0), e(s(0)), e(s(s(0))), …`

At tick `N` the observer holds the finite word `e(0) e(1) … e(N)`. The
experience is this word and the rule that extends it by one letter per tick.

It must satisfy six conditions.

**(X1) Nothing unrendered.** Every reading is the projection of a rendered
state: `e(n) = p(ρ(n))`. Experience is not a further primitive, and adds
nothing to the simulation that the projection did not select from it.

**(X2) Finite at every tick, so never faithful.** `Y` is finite. Hence `e` is
not injective: infinitely many ticks share finitely many readings
(pigeonhole). The simulation is faithful (S2); the experience of it is not.
What the simulation keeps, the experience gives up in exchange for a finite
answer at each tick.

**(X3) Exact registration.** Every reading `e(n)` is decided by finitely many
integer comparisons from the instructure and the observer's cell boundaries,
and no rendered state lies on a cell boundary. The verified instance is the
side bit: `e(n)` is the parity of `a = ⌊2n√d⌋`, certified by
`a² ≤ 4n²d < (a+1)²` (`FloorPos`), and the walker is never on the `½` wall
(`wall_never_hit`, `fixed_points_never_occupied`). For any rational cell
boundary `q`, `n√d = q + k` with `k ∈ ℤ` forces `n = 0`
(`coincidence_only_at_origin`), so no tick `n ≥ 1` ever produces an
ambiguous reading.

**(X4) Forward only.** The record is extended only at its end, by the
carrier's step. A reading at tick `n` is never revised by a later tick, and
there is no step from tick `0` backward. The carrier is the one direction
that only goes one way. This is the formal content of "forward is the
carrier" in *Discrete Evidence in Neuroscience* §8.

**(X5) The question belongs to the observer.** The instructure fixes `ρ`
(up to orientation); the observer fixes `p`. Two observers of the same
simulation, with different cells, keep different records, and the long-run
frequency of each reading is the size of its cell. For the near-meeting
reading with window `ε` that frequency is `2ε`. The frequency statement is
the equidistribution theorem (Weyl), open in the roadmap ledger. That the
count depends on `ε` is what "the window belongs to the observer" means.

**(X6) Never eventually periodic, though never new letter by letter.** Every
letter of the record has occurred before, or will occur again, because `Y`
is finite (X2). The record as a whole, however, is not eventually periodic.
For the side bit of a non-square `d`, suppose `⌊2n√d⌋ mod 2` had an eventual
period `P`. Then the bit would be constant along each progression
`n ≡ r (mod P)`. Along such a progression the phase `n√d mod 1` advances by
`P√d`, which is irrational, so it comes arbitrarily close to every point of
the circle and lands on both sides of the wall: the bit cannot be constant.
The finite record never settles into a cycle because the rendering behind
it never does. At the level of the rendering, the meeting phase never
revisits any value (`meeting_faithful`).

## Mirror experiences

The symmetry group of the instructure acts on experiences by relabelling,
tick by tick:

- A single sign flip inverts a walker's side bit at every tick
  (`flip_inverts_side`). The mirror-image simulation is experienced as the
  same record with `above` and `below` exchanged.
- The Phantom Middle (flip both walkers) leaves the in-step bit unchanged at
  every tick, and a single flip inverts it (`phantom_middle_preserves_inStep`).
- Exchanging the two walkers fixes the shared coordinate `D₁ = a₁ + a₂`,
  negates the depth `D₂ = a₁ − a₂`, and leaves the in-step gate unchanged
  (§15b of `Boundary.lean`).

So the mirror-image simulations of one instructure are experienced as
relabellings of one another, and a reading that every symmetry leaves
unchanged is the same in every mirror world. Such readings are the part of
experience that belongs to the instructure rather than to the orientation.

## The four roles

| Role | What it is | Size | Orientation-dependent? | Faithful? |
|---|---|---|---|---|
| Instructure `I` | Finite integer datum, the building rule | Finite | No | Not applicable |
| Simulation `S_{I,ι}` | Rendering `ρ : Λ → Φ` of a countable carrier | Countable states in an uncountable `Φ` | Yes | Yes (S2) |
| Projection `p : Φ → Y` | Exact, accountable, irreversible reading | `Y` chosen by the observer | Depends on `p` | No (P3) |
| Experience `e = p ∘ ρ` | Tick-by-tick record of the readings | Finite word at every tick | Yes, up to relabelling | No (X2) |

The chain begins and ends with finite integer data. The instructure is a
finite datum, and at every tick an experience is a finite word decided from
integers (X3). Between them, the simulation passes through a phase space that
is never realized (S4). In discrete-first terms, the continuum appears only
in the middle of the chain, as the rendering, and never at either end.

## Worked example: the trap seen by a two-bit observer

The trap's instructure is `I = (30, 33)`. The observer reads two side bits:
whether walker 1 and walker 2 are above their `½` walls, `Y = {0, 1}²`. Each
bit is the parity of `a = ⌊2n√d⌋`, computed with an integer square root of
`4n²d`, as in `FloorPos`. The in-step bit is `1` when the two side bits agree.

| Tick `n` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `⌊2n√30⌋` | 10 | 21 | 32 | 43 | 54 | 65 | 76 | 87 | 98 | 109 | 120 | 131 |
| `⌊2n√33⌋` | 11 | 22 | 34 | 45 | 57 | 68 | 80 | 91 | 103 | 114 | 126 | 137 |
| Side bit 1 | 0 | 1 | 0 | 1 | 0 | 1 | 0 | 1 | 0 | 1 | 0 | 1 |
| Side bit 2 | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 1 |
| In step | 0 | 0 | 1 | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 1 | 1 |

- **(X3)** Every entry is an integer comparison. In every case
  `a² < 4n²d < (a+1)²` holds strictly, so no reading sits on the wall.
- **(X6)** The in-step record shows the near-periodic `0011` pattern of the
  Phantom Middle puzzle, and side bit 1 looks like `0101…`. Both patterns
  break for the first time at tick 22. In the first 200,000 ticks the
  in-step record has no eventual period of length up to 5,000, and the
  fraction of in-step ticks is 0.499985.
- **(X2)** The observer sees four readings, each used about a quarter of the
  time (499, 502, 502 and 497 times in the first 2,000 ticks), so every
  reading repeats endlessly, while the rendering behind it never repeats.
- **Mirror.** Flipping walker 1 turns side bit 1 into `1010…`, and inverts
  every in-step reading. Flipping both walkers leaves the in-step row as it
  is.

The numbers in this section were computed exactly with integer square roots
(`math.isqrt`) on 2026-11-01. They are computational, not kernel-checked.

## Reflexive reading

> **Interpretation.** An instructure is built from self-relations,
> `xᵢ · xᵢ = dᵢ`. An experience ends in self-comparisons: each reading
> compares a rendered state with a boundary the observer has drawn, and the
> in-step reading compares the two walkers with each other. The chain from
> instructure to experience therefore starts with a generator's relation to
> itself and ends with an observer's relation to its own question. *Discrete
> Evidence in Neuroscience* proposes that the brain is such an observer and
> that experienced reality is such a record: "the brain projects experienced
> reality". That proposal is interpretive. The definition above is what it
> would be a proposal *about*.

## Verification status

| Component | Status |
|---|---|
| (X1) `e = p ∘ ρ` | True by construction |
| (X2) `e` is not injective when `Y` is finite | Proved by hand (pigeonhole). A quick target |
| (X3) side bit decided in integers, never on the wall | **Verified**, bare Lean: `FloorPos`, `wall_never_hit`, `fixed_points_never_occupied` (`SimulationExchange/SimulationExchange/Boundary.lean`) |
| (X3) no rational boundary is hit at any tick `n ≥ 1` | **Verified**, bare Lean: `coincidence_only_at_origin` (`Walkers.lean`) |
| (X4) forward only | True by construction for `Λ = ℕ` |
| (X5) long-run frequency equals cell size (`2ε` for near-meetings) | Standard (Weyl equidistribution); not formalized; open in `ROADMAP_LEDGER.md` |
| (X6) the meeting phase never revisits a value | **Verified**, bare Lean: `meeting_faithful` (`Meeting.lean`) |
| (X6) the side-bit record is not eventually periodic | Proved by hand, using density of an irrational rotation of the circle (standard, one-dimensional Kronecker; not formalized). A moderate target |
| Mirror experiences: side bit, in-step bit, walker exchange | **Verified**, bare Lean: `flip_inverts_side`, `phantom_middle_preserves_inStep`, §15b of `Boundary.lean` |
| Worked example | Computational (exact integer square roots); not kernel-checked |
| Experience as human or animal experience | Interpretive; see *Discrete Evidence in Neuroscience* §2, §8 |

See [`Instructure_Formal_Definition.md`](Instructure_Formal_Definition.md),
[`Simulation_Formal_Definition.md`](Simulation_Formal_Definition.md) and
[`Projection_Formal_Definition.md`](Projection_Formal_Definition.md) for the
three roles an experience is composed from.
