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
| `SimulationExchange/` | **New.** Standalone bare-Lean Lake package (own `lakefile.toml`, no Mathlib): two incommensurable walkers rendered from one shared carrier tick. `descent` generalizes the Verified Edition's Theorem 7.4 (`d = 2`) to *every* non-square `d`; `faithful` (simulation condition S2, any char-0 commutative ring) and `no_direct_rule` (no rational affine rule links the walkers) build on it; `Model.lean` gives a kernel-checked model of instructure condition (E1), `Inst d₁ d₂`, as a characteristic-0 commutative ring (not proved to be a field). `Walkers.lean` adds coincidence-only-at-origin and dominance-never-ties; `Boundary.lean` adds the exact-integer 0.5-boundary results (never hitting ½, the Phantom Middle preserving "in step" tick-by-tick). Every hypothesis dropped has a ring-level counterexample. 53 declarations, trust footprint `[propext, Classical.choice, Quot.sound]` (several use no axioms at all); `leanchecker --fresh` exits 0 on all three top-level modules. Not yet built: the Mathlib bridge instantiating `faithful`/`no_direct_rule` at `R = ℝ`, and the asymptotic ½ in-step frequency (needs Weyl equidistribution). |

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
