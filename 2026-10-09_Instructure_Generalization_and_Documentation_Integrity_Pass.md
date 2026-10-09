# Instructure Generalization (`(2,3)` → Any Independent Pair) and Documentation Integrity Pass

**Date:** 2026-10-09
**Project:** `PrimitiveReflexivity` (root repo docs/prose) and
`Theta__0_Photon/Theta0Photon` (four new Lean files)
**Toolchain:** `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a3` (pinned)

A cross-project, fuller-detail copy of this summary — including the Phase
1–2 review/companion-doc work and all engineering snags — is filed in
`Compiler/Build_Summaries/2026-10-09_Instructure_Generalization_and_Documentation_Integrity_Pass.md`,
per this project tree's standing build-summary convention. This copy
summarizes the same session for readers inside this repo specifically.

## Objective

Review an external edit to the main paper's prose for accuracy and tone;
track two previously-untracked companion definition documents
(`Instructure`, `Simulation`) into the repo as Markdown; build a one-page
verification/roadmap ledger from them; then execute that ledger's own
highest-leverage item — generalizing four `(2,3)`-specific Lean files
(`FieldTower.lean`, `GaloisGroup.lean`, `PhantomFixedField.lean`,
`PhantomTriadicBridge.lean`) to hold for *any* independent non-square pair
`(d₁,d₂)` — and sync every document that referenced the old `(2,3)`-only
scope so nothing in the repo overclaims or underclaims what's proved.

## What Was Built

- **`prose_fixes.patch` review and merge** (commit `a510130`): verified an
  external patch's scope notes against the actual Lean source line by line;
  caught and reverted one overreach (striking an Interpretation-box
  synthesis claim in §12 on Tier-1/formalization grounds that don't apply to
  an Interpretation box, per the paper's own Section 1 contract); kept the
  patch's genuine precision fixes.
- **Companion docs tracked** (commit `fc27053`): `Instructure_Formal_Definition.md`
  and `Simulation_Formal_Definition.md`, converted from the original
  `.pdf`/`.docx` sources, cross-linked to each other and the main paper.
- **`ROADMAP_LEDGER.md`** (commit `6fd17bb`): a four-tier map of what's
  kernel-checked vs. interpretive vs. a still-general framework vs. applied
  outside Lean, with an explicit generalization roadmap.
- **Four new Lean files**, each reparametrizing a `(2,3)`-specific file to
  arbitrary `d₁ d₂ : ℕ` under the independence hypotheses `¬IsSquare d₁`,
  `¬IsSquare d₂`, `¬IsSquare (d₁*d₂)`:
  - `GeneralFieldTower.lean` (`b5d1ceb`) — `[ℚ(√d₁,√d₂):ℚ]=4` for any pair.
  - `GeneralGaloisGroup.lean` (`4ab9eca`) — `Gal(ℚ(√d₁,√d₂)/ℚ)≅V₄`, the
    Phantom Middle built parametrically.
  - `GeneralPhantomFixedField.lean` (`2e992e4`) — the Phantom Middle's fixed
    field is `ℚ(√d₁·√d₂)` for any pair.
  - `GeneralPhantomTriadicBridge.lean` (`95bc4a1`) — the product/sum split
    vs. the Phantom Middle, for any pair.

  Every one of the four carries a `(2,3)`-instantiated sanity-check theorem
  checked at the *exact* type of the original `(2,3)`-only file's own object
  (e.g. `GeneralGaloisGroup.lean`'s `card_Gal_eq_four_at_2_3` is stated at
  `_root_.K ≃ₐ[ℚ] _root_.K`, literally `GaloisGroup.lean`'s own automorphism
  group, not just a matching numeral). All four build clean; `#print axioms`
  on every theorem reports `[propext, Classical.choice, Quot.sound]` only —
  zero `sorryAx`, zero new axioms.

- **Documentation sync** (commits `c8df4fb`, `9673d80`): updated
  `ROADMAP_LEDGER.md`, `Instructure_Formal_Definition.md`'s verification
  table, and `Foundations_of_Primitive_Reflexivity_Verified_Edition.md`'s
  Abstract/§9/§11.6/§11.10/§13/Appendix B — in every case *adding* the
  general-pair citations alongside the original `(2,3)` ones rather than
  overwriting them, and deliberately **not** generalizing the one sentence
  that doesn't hold in general (§11.10's `√5 ∉ K` observation, true only for
  the concrete `(2,3)` instance).

See the `Compiler/Build_Summaries/` copy for the full list of Lean-plumbing
bugs hit and fixed along the way (a scripted rename clobbering an unrelated
Mathlib named argument, `variable`/`include`/docstring-ordering rules, a
`simp` recursion-depth blowup, and a missing `open` that `autoImplicit`
silently papered over rather than erroring on — caught only via `#print
axioms`, not the build exit code).

## What Was Tested

```
lake build                                                   # root project, 2748 jobs, clean
lake build Theta0Photon.Algebra.GeneralFieldTower             # clean
lake build Theta0Photon.Algebra.GeneralGaloisGroup             # clean
lake build Theta0Photon.Algebra.GeneralPhantomFixedField       # clean
lake build Theta0Photon.Algebra.GeneralPhantomTriadicBridge    # clean
lake build Theta0Photon                                        # full library, 2633 jobs, clean
```

**Scope limit, stated once:** this covers the two-generator (`k=2`) case
only. General `k>2` is flagged in `ROADMAP_LEDGER.md` as a genuinely new
inductive argument, not implied as done.

## Final State

Nine commits this session on `master` (`a510130` through `9673d80`; see the
`Build_Summaries` copy for the full ordered list). Pushed to `origin master`:

```
To https://github.com/MosesDSI/primitive-reflexivity-lean4.git
   a510130..9673d80  master -> master
```

Working tree clean except the same pre-existing untracked scratch files
present at session start. Both the root `PrimitiveReflexivity` project and
the full `Theta0Photon` library build clean as of `9673d80`, the current
`HEAD`.
