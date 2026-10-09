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
| `R3_bare_lean/`, `Section_VI_Incommensurability/` | Standalone, no-axiom: A-metric independence across metric/order/algebraic decorations; Polar/Axial clock incommensurability |

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
  §11.10 relating that split to the Phantom Middle for `(2,3)`.
- **The instructure/reflexivity parallel.** `Instructure_Formal_Definition.md`'s
  "Reflexive reading" box: each generator's `xᵢ·xᵢ=dᵢ` read as a self-relation
  in the same sense as `x ℛ x`.

**Nothing here needs new Lean work to be legitimate.** It needs to stay
internally coherent and clearly marked, which is what the §12 restoration and
the Instructure refinement were both about.

---

## Tier 3 — Generalization Layer

`Instructure_Formal_Definition.md` and `Simulation_Formal_Definition.md`.
These take the one Lean-verified instance (`(2,3)`) and state it as a general
framework. Each document's own verification-status table is the authority
here; this is a condensed cross-reference.

| Claim | Status |
|---|---|
| `k`-generator instructure `I=(d₁,…,dₖ)`, independence condition | Framework definition, not a theorem |
| `K_I` has degree `2ᵏ`, `G_I≅(ℤ/2)ᵏ`, for general `k` | **Standard; not formalized** |
| Galois ladder (instructure / mediator `⟨π⟩` / simulation, fixed fields `ℚ`, `ℚ(√(d₁d₂))`, `K_I`) | **Verified only for `(d₁,d₂)=(2,3)`**, via `fixedField_phantom_middle`, `stabilizer_sqrt6K` |
| Simulation 5-tuple `(Λ,s,Φ,F,ρ)`, conditions (S1)–(S4) | Framework definition, not a theorem |
| (S1) equivariance, (S2) faithfulness, (S4) non-realization, for the `√30/√33` trap | Not formalized; "quick target" per the Simulation doc's own table |
| (S3) density via Kronecker | **Standard; not formalized**, for the trap or in general |

Tier 3 is, honestly, a roadmap disguised as a definition: it's the shape a
future Lean development would fill, with the `(2,3)` case as the only
currently-occupied cell.

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

## Next Upgrade Targets

The single highest-leverage move available is collapsing Tier 3's `(2,3)`
special case into a general theorem, which would promote the Galois-ladder
row above from Tier 3 to Tier 1 for every independent pair, not just one.

**Target: generalize `GaloisGroup.lean` and `PhantomFixedField.lean` from
`(2,3)` to any independent non-square pair `(p,q)`.**

Concretely, in dependency order:

1. **Generalize the field tower.** `FieldTower.lean`'s `sqrt3_notMem` and
   `sqrt2_sqrt3_finrank` are proved for the fixed pair `(2,3)`. The needed
   generalization is: for non-square `p`, non-square `q`, and `p·q`
   non-square, `√q ∉ ℚ(√p)` and `[ℚ(√p,√q):ℚ]=4`. The proof shape (tower law
   + the existing `triadic_ground_irreducible`/`sqrt_finrank` machinery) is
   already in the repo for the `(2,3)` instance; this step is re-deriving it
   parametrically rather than inventing a new argument.
2. **Generalize the Galois group construction.** `GaloisGroup.lean`'s `σ`,
   `τ`, `phantom_middle`, and `card_Gal_eq_four`/`IsKleinFour` are built via
   explicit `IntermediateField.equivOfEq` constructions specific to `K`. These
   need to become a parametrized construction `σ_{p,q}`, `τ_{p,q}`,
   `phantom_middle_{p,q}` over the field from step 1, with the same explicit
   `AlgEquiv` pattern (the file's own docstring already documents why the
   naive `AlgEquiv.refl`-based shortcut doesn't work — that caution carries
   over unchanged).
3. **Generalize the fixed-field result.** `PhantomFixedField.lean`'s
   `sqrt6K`/`stabilizer_sqrt6K`/`fixedField_phantom_middle` machinery
   generalizes to `sqrt_{pq}K := √p·√q` and a parametrized stabilizer/fixed-
   field pair, following the same `map_mul`-pushed-through-flip-lemmas
   argument used for `(2,3)`.
4. **(Optional, lower priority) Generalize the triadic bridge.**
   `PhantomTriadicBridge.lean` is already explicitly scoped to `(2,3)` by its
   own docstring; extending it to arbitrary `(p,q)` would require
   `TriadicClosure.lean`'s machinery to also be read for general `n,m`, which
   it already supports — so this step is mostly wiring, not new math.

Each step is a reparametrization of an existing, working proof — not new
mathematical content — which is what makes this the most tractable path from
Tier 3 to Tier 1 on the board right now. Completing steps 1–3 would let
`Instructure_Formal_Definition.md`'s verification table replace "Standard;
not formalized" with a real Lean citation for the general-`k=2` Galois
ladder, and would be the natural prerequisite for tackling general `k>2`
afterward.
