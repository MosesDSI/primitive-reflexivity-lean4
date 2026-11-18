# Primitive Reflexivity — Verification & Roadmap Ledger

One-page map of what this project currently is: what's kernel-checked, what's
interpretive synthesis, what's a general framework still waiting on its
general-case proofs, and what's been built on top of all of it.

> **Note on "Tier."** The four tiers below are an epistemic-status axis
> (how a claim is justified), not the Verified Edition's own "Tier 1 /
> Tier 2" labels (which denote *checking method* — Mathlib-dependent build vs.
> standalone bare-Lean file). A result can be Ledger Tier 1 and paper Tier 1
> or Tier 2 at the same time; the two labels answer different questions.

---

## Tier 1 — Machine-Verified Kernel Core

Everything here compiles with zero `sorry`, zero `axiom`, zero
`native_decide`, trust footprint `[propext, Classical.choice, Quot.sound]`
(or, for the bare-Lean files, no axioms at all), and is re-checked on every
push.

| File | What's verified |
|---|---|
| `PrimitiveReflexivity/Foundations.lean` | Reflexivity axioms (R1), diagonal minimality/transport, prime incompressibility, Manhattan/diagonal incommensurability, `(ℝ,+) ≇ U(1)`, triadic geometric-mean bridge, mediator defect positivity |
| `PrimitiveReflexivity/Discrete/OrderObstruction.lean` | The QS ordered field (`ℚ(√2)` from scratch, bare Lean, no Mathlib): field laws, total order, rational density, the abstract retraction-obstruction theorem |
| `PrimitiveReflexivity/Discrete/HarmonicCenter.lean`, `Geometry/SquareUnfolding.lean` | Discrete harmonic centers; isometric boundary-unfolding of the square |
| `Theta__0_Photon/.../GroundAxiom.lean`, `FieldTower.lean` | `x²−n` irreducible for every non-square `n`; `[ℚ(√d):ℚ]=2` for every non-square `d`; the specific `[ℚ(√2,√3):ℚ]=4` tower |
| `Theta__0_Photon/.../GaloisGroup.lean` | `K=ℚ(√2,√3)` is Galois over `ℚ` with Klein four-group `Gal(K/ℚ)`; `σ`, `τ`, `phantom_middle := σ∘τ` constructed explicitly |
| `Theta__0_Photon/.../PhantomFixedField.lean` | The Phantom Middle fixes exactly `√2·√3`; it's the unique non-identity automorphism doing so; its fixed field is `ℚ(√2·√3)`, elementwise form `a+b·√2·√3` |
| `Theta__0_Photon/.../PhantomTriadicBridge.lean` | For the pair `(2,3)` only: the Phantom Middle fixes the triadic product coordinate and negates the triadic sum coordinate |
| `Theta__0_Photon/.../ChiralSign.lean`, `TriadicClosure.lean`, `Incommensurability.lean`, `ContinuumBridge.lean`, `CenteredKernel.lean` | Determinant sign under row permutation; exact multiplicative / defective additive triadic closure; countable↔uncountable operational orthogonality; `ℝ³` has no structure-preserving lattice bijection |
| `Theta__0_Photon/.../GeneralFieldTower.lean` | **New.** `[ℚ(√d₁,√d₂):ℚ]=4` and `√d₂∉ℚ(√d₁)` for *any* independent non-square pair `(d₁,d₂)`, not just `(2,3)` — generalizes `FieldTower.lean`'s §2–§3 |
| `Theta__0_Photon/.../GeneralGaloisGroup.lean` | **New.** `Gal(ℚ(√d₁,√d₂)/ℚ)≅V₄` for any independent pair; `sigma_K`, `tau_K`, `phantom_middle` constructed parametrically; `isGalois_K`/`isKleinFour_K` as theorems (not `instance`s — see the file's own docstring for why) |
| `Theta__0_Photon/.../GeneralPhantomFixedField.lean` | **New.** The Phantom Middle's fixed field is `ℚ(√d₁·√d₂)` for any independent pair; `stabilizer_sqrt_prod` (uniqueness), `phantom_middle_fixed_iff` (elementwise form) |
| `Theta__0_Photon/.../GeneralPhantomTriadicBridge.lean` | **New.** The Phantom Middle fixes the triadic product coordinate and reverses the sum coordinate, for any independent pair — not just `(2,3)` |
| `R3_bare_lean/`, `Section_VI_Incommensurability/` | Standalone, no-axiom: A-metric independence across metric/order/algebraic decorations; Polar/Axial clock incommensurability |
| `SimulationExchange/` | **New.** Standalone bare-Lean Lake package (own `lakefile.toml`, no Mathlib): two incommensurable walkers rendered from one shared carrier tick. `descent` generalizes the Verified Edition's Theorem 7.4 (`d = 2`) to *every* non-square `d`; `faithful` (simulation condition S2, any char-0 commutative ring) and `no_direct_rule` (no rational affine rule links the walkers) build on it; `Model.lean` gives a kernel-checked model of instructure condition (E1), `Inst d₁ d₂`, as a characteristic-0 commutative ring (not proved to be a field). `Walkers.lean` adds coincidence-only-at-origin and dominance-never-ties; `Boundary.lean` adds the exact-integer 0.5-boundary results (never hitting ½, the Phantom Middle preserving "in step" tick-by-tick). `Meeting.lean` (2026-10-11) adds `meeting_faithful`: the separation walker (step `s − t`, the D2 component) never revisits a phase, needing **only** `NonSquare (d₁·d₂)` — neither walker has to be irrational on its own (`meeting_faithful_rational_first`, `(4, 2)`). `Switching.lean` (2026-10-12) formalizes the four worlds as column sign-flips `switch p q` on `Inst d₁ d₂`: each is a ring map fixing the integers, commutes with walkers, composes by XOR, is an involution, and has the stated fixed sets (`pi_fixed_iff`: π fixes exactly `b = c = 0`); `switch_unique` shows the table is forced (any additive map with `f 1 = 1`, `x₁ ↦ ±x₁`, `x₂ ↦ ±x₂` and respecting `x₁·x₂` is exactly the corresponding switch). The table needs **no** hypothesis on `(d₁, d₂)`. `Boundary.lean` §15b (2026-10-13) adds parity gate preservation: exchanging the walkers fixes the shared floor coordinate `D₁ = a₁ + a₂`, negates the depth `D₂ = a₁ − a₂`, keeps the tick, and leaves the in-step gate (exactly the parity of `D₂`, `inStep_iff_D₂_even`) unchanged; no hypothesis on `(d₁, d₂)`. Every hypothesis dropped has a ring-level counterexample. 93 declarations, trust footprint `[propext, Classical.choice, Quot.sound]` (several use no axioms at all); `leanchecker --fresh` exits 0 on `Instances`, `Walkers`, `Boundary`, `Meeting` and `Switching`. Not yet built: the asymptotic ½ in-step frequency (needs Weyl equidistribution); that the four switches are the *only* ring automorphisms of `Inst d₁ d₂` (needs the independence conditions). |
| `Theta__0_Photon/.../SimulationExchangeBridge.lean` | **New.** The Mathlib bridge for the row above: instantiates `SimulationExchange.faithful`/`no_direct_rule` at `R = ℝ`, `s = √d₁`, `t = √d₂` (`faithful_real`, `no_direct_rule_real`), bridges `SimulationExchange.NonSquare` to Mathlib's `¬ IsSquare` (`nonSquare_iff_not_isSquare`), states the `Int.fract` corollaries matching `Simulation_Formal_Definition.md`'s S2 row (`fract_faithful`, `fract_no_direct_rule`), instantiates `meeting_faithful` the same way (`meeting_faithful_real`, with its `Int.fract` form `fract_meeting_faithful`: `fract(n(√d₁−√d₂)) = fract(m(√d₁−√d₂)) → n = m`, needing only `¬ IsSquare (d₁·d₂)`), and cross-checks `no_direct_rule_real` against `GeneralFieldTower.sqrt_notMem` without re-proving it (`sqrt_notMem_agrees_with_no_direct_rule`: clearing denominators in a hypothetical `√d₂ ∈ ℚ⟮√d₁⟯` produces exactly the integer rule `no_direct_rule_real` forbids at tick 1). Added as a local path-dependency of `Theta__0_Photon` on `SimulationExchange/`. Trust footprint `[propext, Classical.choice, Quot.sound]`; `leanchecker --fresh` exits 0. |
| `LTromino/` | **New** (2026-10-15). A core-only Lake package (no Mathlib) that requires `SimulationExchange/` by local path. It was built outside the repo (claude.ai), then verified and placed by Claude Code. `Base.lean`: D₄ on the 2×2 as three bits; orientation read from the corner cycle, with `det_eq_sign`; the chiral diagonals; the onto map D₄ → V₄ with kernel {id, π}, so π is the centre; the L-tromino orientation invariants; necessity witnesses. `Tiling.lean`: deficient-board tiling for every n (`tile_correct`), centre-cell geometry (`touches_middle_iff`) and the area identity 3·tcount n + 1 = 4ⁿ. `Equivariance.lean`: `tile_equivariant`, under which the tiling transforms with its hole, up to `List.Perm`. `DiagonalBridge.lean`: an integer counterpart of the CenteredKernel split. It does not import CenteredKernel. `WalkerBridge.lean`: Two Walkers §4.3. Each walker matrix is read off `Inst.switch` and the walker exchange (`switch_represents`, `exchange_switch_represents`, for all elements and all `d₁ d₂`), and its determinant is −1 exactly for the reversing symmetries (`universal_walker_flip_eq_sign`). **208 theorems, every one of them axiom-free** (`#print axioms` prints "does not depend on any axioms" for each). By module: Base 41, Tiling 77, Equivariance 60 (the 22 original statements, unchanged, plus 38 local helpers that replace propext-carrying core list lemmas and `simp`/`omega`), DiagonalBridge 13, WalkerBridge 17. `leanchecker --fresh` exits 0 on all five modules. CI enforces zero axioms on **every** declaration (400, including definitions and generated lemmas): the `ltromino` job runs axiom-audit with an empty allowlist. `Sym`, `Tromino` and `WalkerMatrix` are declared with `genInjectivity false`, because Lean's auto-generated `mk.injEq` lemmas use `propext`. See `docs/notes/LTromino_Axiom_Audit_Scope_and_CI_Enforcement.md`. |
| `ProjectionNecessity_bare_lean/` | **New** (2026-11-18). A core-only Lake package with no dependencies (no Mathlib, no Batteries, nothing from `SimulationExchange/`). Library root `ProjectionNecessity`; modules `Step1`–`Step7c` and `ZeroInt` (zero-axiom `Nat`/`Int` arithmetic, namespace `DSISVerification.ZeroInt`). **Zero axioms on every declaration:** all 219 declarations under the `ProjectionNecessity` module prefix (theorems, definitions and every generated helper) depend on no axioms. CI enforces this in the `projection-necessity` job: `axiom-audit` with the empty allowlist `","`, plus `leanchecker`. Steps 1–7c use no `simp`, `omega`, `decide`, `by_cases`, `grind` or ZeroInt macros, and no `Nat` subtraction. **Kernel-checked.** *Steps 1–4:* for any response map `r : Φ → R`, the cells of `r` partition the states. Anything that reads the state only through `r` is constant on cells and factors uniquely through the constructed projection `project r : Φ → Cell r`, which is onto and whose fibres are exactly the cells; it is built without quotient types (`project_eq_iff`, `factorization`, `factorization_unique`). With finitely many responses (`AtMostResponses`) and an injective sequence of states (`DistinctStates`), two distinct states share a cell, and no map from cells back to states recovers every state (`two_states_share_a_cell`, `projection_not_reversible`, via a constructive pigeonhole, `pigeonhole`). *Step 5:* a symmetry of `r` induces a unique map on cells that commutes with the projection (`project_equivariant`, `cellMap_unique`); the projection is invariant exactly when the response is (`project_invariant_iff`). *Step 6:* given an involution on responses, a symmetry carries a `Hand` (keep or reverse), and hands compose like signs, reverse after reverse being keep (`hasHand_comp`). If no state is on the wall (`OffTheWall`), a reversing symmetry moves every cell and no symmetry has both hands (`reverse_moves_every_cell`, `hand_well_defined`). *Step 7, the two walkers:* `NonSquare d → 0 < n → NonSquare (4n²d)` by a subtraction-free descent (`no_square_multiple`, `nonSquare_tick`, 7c). This fixes the flip-floor identity `a' = a` (`flip_floor_of_nonSquare`, 7a). It also forces `Hand.reverse` for a single flip and `Hand.keep` for the Phantom Middle on the side and in-step bits (`side_hasHand_reverse_of_nonSquare`, `inStep_flip₁_reverse_of_nonSquare`, `inStep_phantom_keep_of_nonSquare`, 7b). Necessity counterexamples: `side_flip_needs_flipFloor` and `nonSquare_tick_needs_nonSquare` at `d = 4`, and `nonSquare_tick_needs_pos` at `n = 0`. These re-prove, with no axioms, results of the same shape as `SimulationExchange`'s `flip_floor`, `flip_inverts_side`, `phantom_middle_preserves_inStep` and `nonSquare_tick`, whose footprint is `[propext, Classical.choice, Quot.sound]`. **Not claimed here** (see Tier 2): that these theorems formalize self-projection in cybernetic or neural systems, or why a system's response should be finite. Finiteness is a hypothesis of Step 4, not a theorem. |

Each of the four new files carries a `(2,3)`-instantiated sanity-check theorem,
checked at the exact same type as the original `(2,3)`-only file's own
declarations (not just a matching numeral), confirming the generalization
doesn't silently diverge from the instance it generalizes. All four build
clean with trust footprint `[propext, Classical.choice, Quot.sound]` — see
commits `b5d1ceb`, `4ab9eca`, `2e992e4`, `95bc4a1`.

**Everything in this tier is real, re-runnable, kernel-checked mathematics.**
It is also, by construction, narrower than the claims built on top of it —
that gap is what Tiers 2–4 are.

---

## Tier 2 — Interpretive Synthesis

Claims that live in **Interpretation** boxes throughout the Verified
Edition. By the paper's own Section 1 contract, these are explicitly *not*
claims of the formalization — they're retained because they're
explanatorily useful, and the right standard for them is interpretive
coherence, not Lean backing.

- **Discrete-first, node-first ontology.** `x ℛ x` as per se identity prior
  to any external ruler; Sections 2–3's Interpretation boxes.
- **The four-fold incommensurability manifestation.** §12's synthesis claim
  that arithmetic descent, order-theoretic retraction failure,
  field-theoretic non-membership, and cardinality are "the same phenomenon
  recurring at four different levels of mathematical machinery" — restored
  in the `prose-accuracy-pass` merge after a review attempt tried to strike
  it on Tier-1 grounds that don't apply to an Interpretation box.
- **Classical `ℕ` as projection.** §9's reading of `π` as the operation that
  sees the count correctly and discards exactly the mediator defect, with
  §11.10 relating that split to the Phantom Middle for `(2,3)`. **Stale as of
  the Tier 3→1 promotion below:** the Verified Edition's own prose (§9, §11.10,
  the README theorem ledgers) still says "for the pair `(2,3)`" throughout,
  which is no longer the tightest true statement now that
  `GeneralPhantomTriadicBridge.lean` proves the same split for every
  independent pair. Updating the main paper's prose to match is its own
  separate task (see Next Upgrade Targets) — not done as part of this
  ledger/Instructure-table update.
- **The instructure/reflexivity parallel.** `Instructure_Formal_Definition.md`'s
  "Reflexive reading" box: each generator's `xᵢ·xᵢ=dᵢ` read as a self-relation
  in the same sense as `x ℛ x`.
- **Self-projection as a necessity of finite self-reading.** The reading of
  `ProjectionNecessity_bare_lean/` (Tier 1) as "a system that senses itself
  through finitely many readings must project itself, irreversibly and with
  the handedness of its own symmetry": that the response map is the system's
  self-sensing, that the factorization is the projection preceding a
  cybernetic feedback loop, and that this bears on experience in brains or
  machines (`Projection_Formal_Definition.md`, `Experience_Formal_Definition.md`,
  *Discrete Evidence in Neuroscience*). The theorems state the conditional
  "finite response ⟹ unique, irreversible, symmetry-inheriting projection".
  The interpretation of `r` as self-sensing, the closed loop over ticks, and
  the claim that real systems respond finitely are not formalized.

**Nothing here needs new Lean work to be legitimate.** It needs to stay
internally coherent and clearly marked, which is what the §12 restoration and
the Instructure refinement were both about.

---

## Tier 3 — Generalization Layer

`Instructure_Formal_Definition.md` and `Simulation_Formal_Definition.md`.
Originally, these took the one Lean-verified instance (`(2,3)`) and stated it
as a general framework with every cell but `(2,3)` empty. The two-generator
Galois ladder has since been promoted to Tier 1 (below); what's left in Tier 3
is general-`k` (`k>2`) and the `Simulation` side's conditions. Each document's
own verification-status table is the authority here; this is a condensed
cross-reference.

| Claim | Status |
|---|---|
| `k`-generator instructure `I=(d₁,…,dₖ)`, independence condition | Framework definition, not a theorem |
| `K_I` has degree `2ᵏ`, `G_I≅(ℤ/2)ᵏ`, for `k=2` (any independent pair) | **Promoted to Tier 1** — `GeneralFieldTower.sqrt_sqrt_finrank`, `GeneralGaloisGroup.card_Gal_eq_four`/`isKleinFour_K` |
| `K_I` has degree `2ᵏ`, `G_I≅(ℤ/2)ᵏ`, for general `k>2` | **Standard; not formalized** — the one piece of the original 4-step plan genuinely left open |
| Galois ladder (instructure / mediator `⟨π⟩` / simulation, fixed fields `ℚ`, `ℚ(√(d₁d₂))`, `K_I`), for `k=2` | **Promoted to Tier 1** — `GeneralPhantomFixedField.fixedField_phantom_middle`, `stabilizer_sqrt_prod`, for any independent pair, not just `(2,3)` |
| Triadic product/sum split vs. the Phantom Middle, for `k=2` | **Promoted to Tier 1** — `GeneralPhantomTriadicBridge.lean`, for any independent pair |
| Simulation 5-tuple `(Λ,s,Φ,F,ρ)`, conditions (S1)–(S4) | Framework definition, not a theorem |
| (S1) equivariance, (S2) faithfulness, (S4) non-realization, for the `√30/√33` trap | Not formalized; "quick target" per the Simulation doc's own table |
| (S3) density via Kronecker | **Standard; not formalized**, for the trap or in general |
| Projection `(X,⊙,Y,⊕,p)`, conditions (P1)–(P4) (`Projection_Formal_Definition.md`, 2026-11-01) | Framework definition, not a theorem. Each condition has a verified instance (`projection_commutes_on_n`, `correction_identity`, `triadic_addition_not_closed`, `incommensurability_blocks_retraction`, `FloorPos`/`wall_never_hit`); the abstract structure is not formalized. Since 2026-11-18 the (P3) fibre form is also proved in the abstract, with no axioms, for the projection onto the cells of any finite response map (`projection_not_reversible`, `ProjectionNecessity_bare_lean/`, Tier 1); (P1)/(P2) in their operation-and-residue form are not covered there |
| Experience `e = p ∘ ρ`, conditions (X1)–(X6) (`Experience_Formal_Definition.md`, 2026-11-01) | Framework definition, not a theorem. (X3) and the mirror relabellings verified for the side and in-step bits (`Boundary.lean`); (X2) proved by hand (pigeonhole; the pigeonhole and its non-injectivity consequence are kernel-checked with no axioms in `ProjectionNecessity_bare_lean/` Steps 4a–4b, but their instantiation at `e = p ∘ ρ` is not written out); (X5) needs Weyl equidistribution (standard, not formalized; it strengthens the Kronecker density of Next Upgrade Targets item 1); (X6) proved by hand from one-dimensional density |

Tier 3 is still honestly a roadmap disguised as a definition — it's the shape
a future Lean development fills in — but three of its original cells (the
`k=2` Galois ladder, including the triadic bridge) are no longer empty, and
are tracked under Tier 1 now instead of here.

---

## Tier 4 — Applied Computational Layer

The `√30`/`√33` worked example (Instructure doc, "Worked example" section).

- **The instructure.** `I=(30,33)`; independence condition checked by hand
  (`30`, `33`, `990=3²·110` all non-square).
- **The decidability procedure.** Every order question (which side of a wall,
  which side of a midpoint) is settled by finitely many *exact* integer
  computations — integer square roots of `30D²`, `33D²`, `110D²`, tightened
  until forced. This is deterministic, exact-arithmetic decidability per
  tick, not floating-point prediction or approximation: each tick's output is
  a forced integer comparison, not an estimate.
- **Implementation.** JavaScript, outside Lean. 20 digits of precision
  sufficed in the test runs reported. This is the one component of the whole
  project whose correctness rests on an external test run rather than a
  kernel check or a standard-math citation — worth flagging precisely because
  every other tier is careful to say which kind of justification it's
  relying on.

---

## Completed: the `(2,3)` → any-independent-pair generalization

The four-step plan below **is done** (commits `b5d1ceb`, `4ab9eca`,
`2e992e4`, `95bc4a1`). Kept here, marked complete, as the record of how it
went rather than deleted, since the engineering snags (not the math) are the
part worth remembering.

1. ✅ **Field tower** — `GeneralFieldTower.lean`: `√d₂∉ℚ(√d₁)` and
   `[ℚ(√d₁,√d₂):ℚ]=4` for any independent pair. Straightforward
   reparametrization of `FieldTower.lean`'s §2–§3.
2. ✅ **Galois group construction** — `GeneralGaloisGroup.lean`: `σ`, `τ`,
   `phantom_middle` built parametrically, same explicit-`AlgEquiv` pattern as
   `GaloisGroup.lean`. `isGalois_K`/`isKleinFour_K` are theorems, not
   `instance`s, since Lean can't discharge `¬IsSquare d₁` on its own for a
   free `d₁` the way it can for the literal `2`.
3. ✅ **Fixed-field result** — `GeneralPhantomFixedField.lean`:
   `fixedField_phantom_middle`/`stabilizer_sqrt_prod` for any independent
   pair, same `map_mul`-through-flip-lemmas argument.
4. ✅ **Triadic bridge** — `GeneralPhantomTriadicBridge.lean`: close to pure
   wiring, as anticipated — `TriadicClosure.lean` was already general in `n`.

Every step really was a reparametrization, not new mathematical content — the
actual friction was Lean plumbing (a scripted rename clobbering an unrelated
Mathlib named argument, `variable`/`include` scoping rules, a `simp`
recursion-depth blowup), not the proofs themselves. All four files carry a
`(2,3)`-instantiated sanity check against the original file's own
declarations, and all build with trust footprint
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## Next Upgrade Targets

With the `k=2` ladder done, three targets remain open, roughly in order of
tractability:

1. **Kronecker density (S3).** Needed for the Simulation side's density
   condition, for the trap or in general. Standard, not yet formalized —
   likely the next-easiest real theorem on the board, since Mathlib has some
   multi-dimensional equidistribution machinery to build on.
2. **Formalize the trap's exact-decidability procedure (N4) in Lean.**
   Currently implemented and tested only in JavaScript — the one piece of the
   whole project whose correctness rests on an external test run rather than
   a kernel check. Porting the integer-tightening procedure into Lean (even
   just for the `(30,33)` instance) would close that gap.
3. **Generalize `k=2` to general `k`.** Unlike steps 1–4 above, this is a
   genuinely new argument, not a reparametrization: it needs an inductive
   construction of the `2ᵏ`-element sign-flip group and a degree argument by
   induction on `k`, rather than copying the two-generator proof shape.
   Higher effort, lower immediate payoff than the first two targets.
4. **Documentation debt.** The main Verified Edition paper's §9 and §11.10,
   and both READMEs' theorem ledgers, still describe the Phantom
   Middle/triadic connection as holding "for the pair `(2,3)`" — true of what
   `PhantomTriadicBridge.lean` proves, no longer the tightest true statement
   given `GeneralPhantomTriadicBridge.lean`. Updating that prose is a
   separate, deliberate editorial pass (in the spirit of the
   `prose-accuracy-pass` branch), not a side effect of adding new Lean files.
