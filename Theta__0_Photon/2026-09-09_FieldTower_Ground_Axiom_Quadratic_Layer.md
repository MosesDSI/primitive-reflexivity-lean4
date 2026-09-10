# Build Summary — FieldTower.lean: the Degree-4 Tower (Closed) and Its Quadratic Layer

**Date:** 2026-09-09
**Files:** `Theta0Photon/Algebra/GroundAxiom.lean` (new — committed, was previously
only demonstrated in a deleted scratch file), `Theta0Photon/Algebra/FieldTower.lean` (new)
**Objective:** Formalize `Gal(ℚ(√d₁,√d₂)/ℚ) ≅ V₄` with an explicit "Phantom Middle"
`(1,1)` automorphism, for `d₁=2, d₂=3`, built on `triadic_ground_irreducible`.
**Outcome:** Partial, by deliberate decision, not oversight. The degree-2 layer is
fully proved and compiled (`lake build Theta0Photon` / `Main`, 2380/2380 jobs, both
clean). The degree-4 tower, the Galois group computation, and the Klein-four/Phantom
Middle identification are **not** in this file — no theorem for any of them is
stated anywhere, proved or otherwise, because none of them is proved yet. See §3.

---

## 1. What was committed

- **`GroundAxiom.lean`** — the `X² - n` irreducibility theorem from an earlier
  session this same day (verified then, but only ever run in a scratch file and
  deleted — never actually committed to the repo until now). Refactored to expose
  `triadic_no_rational_root` as its own lemma (`FieldTower.lean` needs the
  "no rational root" fact directly, not buried inside the irreducibility proof).
- **`FieldTower.lean`** — for any non-square natural `d`: `sqrt_isIntegral`,
  `sqrt_minpoly` (the genuine use of the ground axiom — see §2), `sqrt_finrank`
  (`[ℚ⟮√d⟯:ℚ] = 2`, exact), instantiated at `d₁=2, d₂=3`. 8 theorems total, 0 `sorry`.

## 2. The actual (non-decorative) structural link to the ground axiom

Unlike `ChiralSign.lean` (which explicitly found *no* formal link to the ground
axiom and said so), this file has a genuine one: `minpoly.eq_of_irreducible_of_monic`
requires a monic, **irreducible** polynomial with the target element as a root to
conclude it *is* the minimal polynomial. Monic and root-having are trivial for
`X² - d` at `√d`; irreducibility is exactly `triadic_ground_irreducible`'s job, and
nothing else in this file supplies it. This is a real, checkable dependency (traced
in the actual `import`/proof-term graph, not asserted).

## 3. Why the degree-4 tower, Galois group, and Klein-four layer are not here

This is the substantive finding of this session, and it is reported plainly rather
than worked around with a `sorry` or a stated-but-unproved theorem (which would be
exactly the "gets by the kernel because of how it was stated" failure mode flagged
in the request):

`[ℚ(√2,√3):ℚ] ≤ 4` follows cheaply (tower law), but `= 4` needs the genuinely
separate fact `√3 ∉ ℚ⟮√2⟯` — the actual content of "multiplicative independence."
Two real routes were investigated (both checked against the real Mathlib source
this session, not assumed):

1. **Explicit-basis route** — show elements of `ℚ⟮√2⟯` have the form `a+b√2`, then a
   classical case split on `a+b√2=√3` (clearing `√2` when `ab≠0`; splitting `a=0` /
   `b=0` otherwise) forces a rational square root of 2, 3, or 6 — each already ruled
   out here (`six_not_square` is in `FieldTower.lean` for exactly this reason,
   despite not being used yet). Getting the `a+b√2` form needs either
   `IntermediateField.adjoin.powerBasis`'s `PowerBasis` API (dependent on
   `Fin (minpoly...).natDegree`, needing care to reindex to `Fin 2`) or
   `IntermediateField.mem_adjoin_simple_iff`'s quotient-of-polynomials
   characterization reduced mod the minimal polynomial. Real, tractable, not yet
   built.
2. **Primitive-element route** — `ℚ⟮√2,√3⟯ = ℚ⟮√2+√3⟯` (via `(√2+√3)³=11√2+9√3`,
   an invertible 2×2 system recovering `√2,√3` from `√2+√3` and its cube), then
   identify `minpoly ℚ (√2+√3) = X⁴-10X²+1` the same way this file identifies
   quadratic minimal polynomials — except this needs **quartic** irreducibility over
   `ℚ`, which the ground axiom (quadratic-only) does not cover. Checked this
   session: no `Decidable`/`decide` shortcut for polynomial irreducibility exists in
   this Mathlib revision, over `ℚ` or via a mod-`p` reduction over a finite field —
   it would need a hand-written quartic irreducibility proof.

Past whichever of these closes the degree-4 count, constructing the automorphisms
themselves as genuine `AlgEquiv`s and assembling `Gal(K/ℚ) ≅ V₄` is a further,
separate stage. Real Mathlib machinery for it was located and confirmed present in
this Mathlib revision (not yet wired to a proof term):
- `IsGalois.card_aut_eq_finrank : [FiniteDimensional F E] → [IsGalois F E] →
  Nat.card Gal(E/F) = finrank F E`
- `IsKleinFour` (`Mathlib.GroupTheory.SpecificGroups.KleinFour`): a group is
  `IsKleinFour` iff `Nat.card = 4 ∧ Monoid.exponent = 2`, and any two `IsKleinFour`
  groups are isomorphic via `IsKleinFour.mulEquiv'` given any identity-preserving
  bijection — this is the natural route to the requested explicit `(1,1)` element,
  since `mulEquiv'` lets a specific bijection (sending the "flip both signs"
  automorphism to `Multiplicative (1,1)`) be chosen deliberately rather than
  obtained only as an abstract `Nonempty` existence claim.

## 4. What was verified

- `lake env lean` on both files individually — clean, zero errors, zero warnings,
  after fixing one real error (`decide` cannot dispatch an unbounded `∃ k : ℕ, ...`;
  fixed with an explicit `nlinarith`-derived bound + `interval_cases`).
- `#print axioms` on all 8 theorems (`GroundAxiom.lean`'s 3 confirmed previously
  this session; `FieldTower.lean`'s 8 confirmed fresh) — every one
  `[propext, Classical.choice, Quot.sound]` only, no `sorryAx`. Stripped from the
  shipped files after verification, same convention as `ChiralSign.lean`.
- `lake build Theta0Photon` and `lake build Main` — **2380/2380 jobs, both clean**
  (grew from 1740 with the new `Mathlib.Analysis.SpecialFunctions.Sqrt` dependency
  chain) — real default-target verification, not just standalone `lake env lean`.

## 5. Files

- `Theta0Photon/Algebra/GroundAxiom.lean` (new)
- `Theta0Photon/Algebra/FieldTower.lean` (new, partial by design — see §3)
- `Theta0Photon.lean` (updated, two new import lines)
- This file.

## 6. Open items (the real next steps, in order)

1. Close `[ℚ(√2,√3):ℚ] = 4` via route 1 or 2 above.
2. Construct the two sign-flip automorphisms as `AlgEquiv`s.
3. Apply `IsGalois.card_aut_eq_finrank` + `IsKleinFour.mulEquiv'` to get the explicit
   isomorphism to `Multiplicative (ZMod 2 × ZMod 2)`, choosing the bijection so the
   "flip both" automorphism lands exactly on `(1,1)` — the requested Phantom Middle
   identification.
4. Decide then whether to generalize `d₁,d₂=2,3` back to arbitrary squarefree,
   multiplicatively-independent naturals (the request's original framing) — `route 1`
   above generalizes cleanly; `route 2`'s quartic-irreducibility step would need to
   become a general argument, not just a single hand-checked polynomial.

---

## Iteration 2 (same day, 2026-09-09): the degree-4 tower, actually closed

Per explicit direction to proceed with the explicit-basis route rather than
leave the degree-4 gap open. **Outcome: fully closed, `[ℚ(√2,√3):ℚ] = 4`
proved exactly, no `sorry`, 10 new theorems, all axiom-checked to the standard
trust base, merged into `FieldTower.lean` and verified via the real
`lake build` (2380/2380 jobs, both `Theta0Photon` and `Main`).**

### What was built

**§2 — the independence fact `√3 ∉ ℚ⟮√2⟯` (the real content of "multiplicative
independence"):**
- `sqrt_ne_ratCast d hd a : (a:ℝ) ≠ Real.sqrt d` — a real-number-level
  restatement of `triadic_no_rational_root`, reused three times below (for
  `d=2,3,6`) instead of re-derived.
- `sqrt2_basis_indep` — `{1, √2}` is `ℚ`-linearly independent in `ℚ⟮√2⟯`, via
  Mathlib's `LinearIndependent.pair_iff'`.
- `sqrt2_basis` — the resulting `Module.Basis (Fin 2) ℚ ℚ⟮√2⟯`, via
  `basisOfLinearIndependentOfCardEqFinrank` (found this session — turns a
  linearly independent family of size `= finrank` directly into a basis,
  avoiding `IntermediateField.adjoin.powerBasis`'s `Fin (minpoly...).natDegree`
  dependent-type reindexing that the previous iteration's write-up flagged as
  the likely friction point).
- `sqrt2_field_eq` — every element of `ℚ⟮√2⟯` has the form `a + c√2` for
  rationals `a, c`, via `Basis.sum_repr`.
- `sqrt3_notMem` — the independence theorem itself: assuming `√3 = a + c√2`,
  squaring and case-splitting on `a·c = 0` forces a rational square root of
  2, 3, or 6, each contradicted directly by `sqrt_ne_ratCast`. The `a=0`
  sub-case needed one extra real-analysis step (`c ≥ 0` from both sides of
  `√3 = c√2` being real square roots, then `Real.sqrt_sq` to get
  `2c = √6` exactly) that wasn't in the original route sketch but was
  required for full rigor.

**§3 — closing the tower, by re-running the §1 pattern one field up:**
- `sqrt3_isIntegral_over_sqrt2`, `X_sq_sub_three_irreducible_over_sqrt2`
  (the genuine use of §2: a root of `X²-3` in `ℚ⟮√2⟯` would force
  `√3 = ±r ∈ ℚ⟮√2⟯`, contradicting `sqrt3_notMem`),
  `sqrt3_minpoly_over_sqrt2`, `sqrt3_finrank_over_sqrt2` — exactly mirror
  `sqrt_isIntegral`/`triadic_ground_irreducible`/`sqrt_minpoly`/`sqrt_finrank`
  from §1, but over base field `ℚ⟮√2⟯` instead of `ℚ`, giving
  `[ℚ⟮√2⟯⟮√3⟯:ℚ⟮√2⟯] = 2`.
- `sqrt2_sqrt3_tower_eq` — `ℚ⟮√2⟯⟮√3⟯.restrictScalars ℚ = ℚ⟮√2,√3⟯`, via
  Mathlib's `adjoin_adjoin_left`-family lemma `adjoin_simple_adjoin_simple`.
- `sqrt2_sqrt3_finrank` — **the degree-4 tower**: tower law
  `[ℚ⟮√2⟯⟮√3⟯:ℚ⟮√2⟯]·[ℚ⟮√2⟯:ℚ] = [ℚ⟮√2,√3⟯:ℚ] = 2·2 = 4`.

### Problems encountered and how they were fixed (compiled at every step, not assumed)

- **`IsIntegral`'s raw existential displays as `eval₂`, but `minpoly.eq_of_irreducible_of_monic`'s
  `hp2` argument displays as `aeval`.** Same underlying fact, two different
  unfolding conventions depending on which lemma produces the goal. Caught by
  reading the actual goal state after each `refine`/`apply`, not assumed to
  match the pattern used one line earlier — required different `simp`/
  `norm_num` lemma sets (`eval₂_sub/pow/X/C` vs the `aeval`-based default
  simp set) for what looks like the same kind of step in `sqrt_isIntegral`
  (base `ℚ`) vs `sqrt3_isIntegral_over_sqrt2` (base `ℚ⟮√2⟯`).
- **A numeral cast gap specific to subfield-valued numerals.** `((3:ℚ⟮√2⟯):ℝ)`
  did not automatically simplify to `(3:ℝ)` under plain `simp`/`exact_mod_cast`
  the way `((3:ℚ):ℝ) = (3:ℝ)` does (ℚ→ℝ casts are far more thoroughly
  `norm_cast`-tagged than a general subfield's coercion). Fixed by explicitly
  adding `map_ofNat` to each affected `simp`/`norm_num` call, and switching one
  `simpa` to `norm_num` where `simpa` alone still left `↑3` unresolved against
  a goal stated as bare `3`.
- **`Basis` resolved to `Module.Basis` mid-session** (this Mathlib revision
  has `structure Basis` declared inside `namespace Module`, with `Basis`
  presumably reachable unqualified elsewhere via an `export` not in scope from
  this file's minimal imports) — a bare `Basis` reference produced a
  confusing cascade of unrelated-looking errors purely from Lean's
  `autoImplicit` silently treating the unknown name as an implicit type
  variable. Fixed by using the fully-qualified `Module.Basis`. A blanket
  find-and-replace for this also corrupted an unrelated `import
  Mathlib.LinearAlgebra.Basis.Defs` line into a nonexistent
  `Mathlib.LinearAlgebra.Module.Basis.Defs` — caught by the resulting "object
  file does not exist" error pointing at a path that doesn't exist on disk,
  not assumed to be a real missing-dependency problem.
- **`Module.finrank ℚ ↥(E.restrictScalars ℚ) = Module.finrank ℚ ↥E`** — needed
  to bridge the tower-law computation (done over `↥ℚ⟮√2⟯⟮√3⟯` directly) back
  to the `restrictScalars`-based `ℚ⟮√2,√3⟯` equality. No named Mathlib lemma
  for this was found (`IntermediateField.finrank_restrictScalars` does not
  exist — a guess that failed). Tested whether the two sides are already
  *definitionally* equal (`restrictScalars` keeps the same `carrier`, per its
  actual definition read directly from `IntermediateField/Basic.lean`) via
  Lean's `show` tactic, which restates a goal only if it's defeq to the
  current one — it succeeded, confirming the hypothesis empirically rather
  than by lemma name, and the direct tower-law computation could proceed
  without needing a named bridging lemma at all.

### Verification

- `lake env lean` on the standalone scratch build — clean after the fixes
  above (iterated ~10 times against real compiler errors, not guessed).
- `#print axioms` on all 10 new theorems individually, before merging into the
  shipped file: every one `[propext, Classical.choice, Quot.sound]` only, no
  `sorryAx`.
- `lake build Theta0Photon.Algebra.FieldTower`, `lake build Theta0Photon`,
  `lake build Main` — **2380/2380 jobs, all three clean**, after merging the
  new §2/§3 content into the existing §1 file and updating its module doc.

### What's still open (unchanged in kind from before, just moved one stage later)

The automorphism/Galois-group/Klein-four/"Phantom Middle" layer is not built.
`FieldTower.lean`'s closing module doc now names the concrete four-step path
(`IsGalois` from splitting-field normality → `IsGalois.card_aut_eq_finrank` →
explicit sign-flip `AlgEquiv`s → `IsKleinFour`/`IsKleinFour.mulEquiv'`), all
four pieces located and confirmed present in this Mathlib revision, none yet
applied to a proof term.

---

## Iteration 3 (same day, 2026-09-09): the Galois group, closed — `Gal(K/ℚ) ≅ V₄`

Per explicit direction to execute the full 4-step path immediately. **Outcome: fully
closed.** `IsGalois ℚ K`, `Monoid.exponent Gal(K/ℚ) = 2`, `IsKleinFour (K ≃ₐ[ℚ] K)`, and
an explicit `Gal(K/ℚ) ≃* Multiplicative (ZMod 2 × ZMod 2)` sending the "Phantom Middle"
automorphism (both generators flipped simultaneously) exactly to `(1,1)` — all proved,
no `sorry`, axiom-checked to the standard trust base, merged into a new file
`Theta0Photon/Algebra/GaloisGroup.lean` and verified via the real `lake build`
(2477/2477 jobs, both `Theta0Photon` and `Main`).

### A real bug caught mid-construction, not glossed over

Building τ (the automorphism fixing `√2`, flipping `√3`) required transporting an
`AlgEquiv` across a `restrictScalars` type-identification (`ℚ⟮√2⟯⟮√3⟯` as a
`ℚ⟮√2⟯`-field vs. `K` as a `ℚ`-field, related by `sqrt2_sqrt3_tower_eq`). The first
attempt did this with ordinary tactics — `rw [← sqrt2_sqrt3_tower_eq]` then `show`/`exact`
on the resulting goal. This **silently type-checked to the identity automorphism**,
not τ: Lean's `rw` tactic tries `rfl` automatically after rewriting, and `AlgEquiv.refl`
is `@[refl]`-tagged, so a goal that happens to become `X ≃ₐ[R] X` for syntactically
identical `X` gets auto-closed by the identity — with no error, no warning, nothing
distinguishing it from a real proof. This is exactly the failure mode named in the
request ("nothing getting by the kernel because of how it was stated") — caught here
only because every constructed automorphism gets an explicit numeric sanity check
(`tau_flips_sqrt3`, `tau_fixes_sqrt2`, `sigma_flips_sqrt2`, `sigma_fixes_sqrt3`) verifying
its action on `√2`/`√3` *before* being trusted for anything downstream, not because the
kernel or `lake build` flagged anything — a green build proved nothing here on its own.
**Fix:** rebuilt the transport in term mode via `IntermediateField.equivOfEq` (which
converts an equality of `IntermediateField`s into a genuine `AlgEquiv` via
`Subalgebra.equivOfEq`, no tactic-triggered `rfl` involved), then re-ran the same
sanity checks — this time getting the real, non-trivial answer confirmed independently.

### What was built

- **τ and σ** (§2–3 of `GaloisGroup.lean`) — each constructed by re-running
  `FieldTower.lean`'s exact minpoly-identification pattern one field up (base
  `ℚ⟮√2⟯` for τ, base `ℚ⟮√3⟯` for σ — the latter needed a small mirrored
  independence corollary, `sqrt2_notMem_sqrt3`, obtained cheaply from `sqrt3_notMem`
  via a containment + equal-finrank argument rather than re-derived from scratch),
  via `algHomAdjoinIntegralEquiv` (root-swap construction) + `AlgHom.bijective`
  (a field endomorphism of a finite extension is automatically bijective once
  injective — found this session in `Mathlib.FieldTheory.Fixed`).
- **`phantom_middle := σ.trans τ`** — verified by direct computation (not assumed
  from "σ flips one, τ flips the other") to flip *both* generators.
- **`IsGalois ℚ K`** — via the converse criterion `IsGalois.of_card_aut_eq_finrank`,
  not by constructing a splitting field: four pairwise-distinct automorphisms
  (`{1, σ, τ, σ∘τ}`, distinguished by their differing action on `√2`/`√3`) give
  `Nat.card Gal(K/ℚ) ≥ 4`; the general upper bound `AlgEquiv.card_le` (any finite
  extension, no Galois assumption needed) gives `≤ [K:ℚ] = 4`; equality is exactly
  Galois-ness by that criterion.
- **`algEquiv_ext_gens`** — two `ℚ`-automorphisms of `K` agreeing on `√2` and `√3`
  are equal, via Mathlib's `IntermediateField.algHom_ext_of_eq_adjoin`. Used to prove
  `σ²=τ²=(σ∘τ)²=1` by checking each side's action on the two generators only.
- **`Monoid.exponent Gal(K/ℚ) = 2`** — the four known elements already exhaust the
  group (`Finset.eq_univ_of_card` from the cardinality result), each squares to `1`,
  and `2` prime pins the exponent to exactly `2` (not `1`, since `σ ≠ 1`) via
  `Monoid.exponent_dvd_iff_forall_pow_eq_one` + `Nat.dvd_prime`.
- **`IsKleinFour (K ≃ₐ[ℚ] K)`** — literally `⟨card_four, exponent_two⟩` once the two
  pieces above exist.
- **`galoisKleinFourEquiv : Gal(K/ℚ) ≃* Multiplicative (ZMod 2 × ZMod 2)`** — via
  `IsKleinFour.mulEquiv`, from a bijection built with **two** chained `Equiv.setValue`
  adjustments (`σ∘τ ↦ (1,1)`, then `1 ↦ 1`), ordered so the identity-preserving
  precondition (`mulEquiv`'s own requirement) is immediate (`Equiv.setValue_eq`), while
  the harder case-split proof — showing the second adjustment doesn't disturb the
  first's placement of `σ∘τ` — was written out explicitly for
  `galoisKleinFourEquiv_phantom_middle` rather than left to `simp` (an earlier attempt
  with a single `setValue` and `by simp` for the identity condition could not be proved,
  correctly reflecting that a single adjustment doesn't establish it).

### Problems encountered and how they were fixed (compiled at every step)

- **The `rfl`-auto-closes-to-identity bug** — see above; the most consequential finding
  of this iteration.
- **Multiple explicit-Type-argument surprises**: `algHomAdjoinIntegralEquiv`,
  `IsGalois.of_card_aut_eq_finrank`, and `IntermediateField.algHom_ext_of_eq_adjoin`
  all take their base field `F` as an *explicit* first argument (not implicit, despite
  reading naturally as inferrable) — each caught via `#check @lemma` showing the real
  elaborated signature after a first application attempt mis-consumed a later
  argument, not guessed a second time.
- **`Fintype.card` numeral gaps**: `Fintype.card (Multiplicative (ZMod 2 ×
  ZMod 2)) = 4` could not be closed by `decide` inside this file's full import context
  (it works in a minimal-import isolated test — some competing, likely non-computable
  instance is picked up transitively) or by bare `simp`; closed instead with an
  explicit `rw [Fintype.card_multiplicative, Fintype.card_prod]; simp [ZMod.card]` chain.
- **`Finset {…}` literal notation needs `DecidableEq` at the *statement* level**, not
  just inside a `by classical` tactic block — a `have` inside a proof can supply it
  locally, but a *theorem's stated type* containing a `Finset` literal elaborates before
  any tactic runs. Fixed with one file-level
  `noncomputable instance : DecidableEq (K ≃ₐ[ℚ] K) := Classical.decEq _`.
- **`Finset.card_insert_of_not_mem` doesn't exist** — this Mathlib revision spells it
  `Finset.card_insert_of_notMem` (matching the `notMem` convention already seen
  elsewhere in this session, e.g. `KleinFour.lean`'s own `mul_notMem_of_exponent_two`).

### Verification

- Every construction compiled incrementally against the real pinned toolchain,
  fixing real reported errors at each step (not assumed correct because a similar
  step worked earlier — the `algHomAdjoinIntegralEquiv` argument order, the
  `Fintype.card` numeral gap, and the `rfl`-identity bug were each different failure
  shapes requiring their own diagnosis).
- `#print axioms` on the load-bearing theorems (`card_Gal_eq_four`,
  `nat_card_Gal_eq_four`, `exponent_Gal_eq_two`, `galoisKleinFourEquiv_phantom_middle`)
  — every one `[propext, Classical.choice, Quot.sound]` only, no `sorryAx`. Checked
  before merging into the shipped file.
- `lake build Theta0Photon` and `lake build Main` — **2477/2477 jobs, both clean**
  (grew from 2380 with the new `Fixed`/`Galois.Basic`/`KleinFour` dependency chain).

### Files

- `Theta0Photon/Algebra/GaloisGroup.lean` (new, ~360 lines).
- `Theta0Photon.lean` (updated, one new import line).
- This file (Iteration 3 section).

### Open items

- The construction is for the concrete pair `d₁=2, d₂=3`, matching the whole session's
  scope (see Iteration 1's note on generalizing back to arbitrary squarefree,
  multiplicatively-independent naturals — unchanged by this iteration).
- `galoisKleinFourEquiv` is one specific, explicitly-chosen isomorphism (not the only
  one satisfying the request) — a different valid choice would send `σ∘τ` to `(1,1)`
  via a different bijection; this one was picked because both required properties
  (identity-preserving, Phantom-Middle-at-`(1,1)`) are proved directly rather than
  by appeal to `Nonempty`/existence alone.

---

## Iteration 4 (same day, 2026-09-09): `Theta0Photon/SetTheory/Incommensurability.lean`

Per explicit direction to move to the next phase: no bijection between a "discrete
count" type and a "continuous/topological measure" type, structure-preserving or
not, plus an explicit connection to today's field tower. **Outcome: built, 4 theorems,
0 `sorry`, standard trust base (two are even axiom-lighter — `Quot.sound` only, no
`propext`/`Classical.choice` needed), clean on the *first* compile attempt (no
iteration needed, unlike every earlier file today) — `lake build Theta0Photon`/`Main`:
2482/2482 jobs, both clean.**

### The real content decision, made explicit rather than left implicit

None of "operationally orthogonal," "`PreservesStructure`," or "discrete count /
continuous measure" are existing Mathlib or standard mathematical terms — this file
had to choose a precise formal meaning for each, and the choices (stated in the
file's own module doc, not only here) were:

- **"Discrete count" / "continuous measure"** → Mathlib's real `Countable A` /
  `Uncountable B` typeclasses (`Uncountable` is literally `¬Countable`).
  `OperationallyOrthogonal A B := Countable A ∧ Uncountable B`.
- **The theorem is proved for *any* `PreservesStructure` predicate**, not one
  specific chosen definition — because `{f : A ≃ B // P f}` is a subtype of `A ≃ B`,
  and *that* ambient type is already empty by a direct cardinality argument
  (`Function.Injective.countable` applied to the equiv's own inverse — the "without
  an intermediate operator" reading used here). Restricting to any extra property can
  only shrink an already-empty type, so no specific choice of `PreservesStructure`
  does real work. Making one specific choice (e.g. picking `Monotone` and presenting
  *that* as the interesting result) would have misstated what actually drives the
  conclusion — so the general lemma is proved first
  (`isEmpty_structurePreserving_of_operationallyOrthogonal`, universally quantified
  over the predicate), and `Monotone` on the concrete `ℕ`/`ℝ` instance is presented
  explicitly as *one* corollary of it, not as the finding itself.
- **"Non-zero quotient spaces… in our field tower"** → connected to `K = ℚ(√2,√3)`
  from `GaloisGroup.lean` directly: `sqrt2_sqrt3_finrank : finrank ℚ K = 4` (reused,
  not re-derived) gives a coordinate identification `K ≃ₗ[ℚ] (Fin 4 → ℚ)` via
  `Module.finBasis`, from which `K` inherits countability (`ℚ` countable, finite
  product of countable types is countable) — making `K` a genuine instance of the
  countable side of this file's theorem, with `ℝ` (the field `K` sits inside) on the
  uncountable side. The "quotient" reading: each layer of the tower is (isomorphic
  to) a polynomial quotient `F[X]/(minpoly)` of nonzero degree (already verified as
  `sqrt2_finrank`/`sqrt3_finrank_over_sqrt2` — genuinely nonzero, not merely nonempty),
  and it is exactly that finite, nonzero dimension that keeps `K` countable rather
  than continuum-sized.

### One thing flagged explicitly, not smoothed over

`isEmpty_equiv_K_real : IsEmpty (K ≃ ℝ)` is **not** a restatement of `K` being a
strict subfield of `ℝ` (already implicit in `K`'s own definition as an
`IntermediateField ℚ ℝ`) — a proper subfield can still have the *same* cardinality as
the whole field in general. The reason no bijection exists here is specifically that
`K` is finite-dimensional over `ℚ`, hence countable; that is the substantive content
being connected to the field tower, not the subfield relationship itself.

### What was built

- `OperationallyOrthogonal A B` — the named hypothesis bundle.
- `isEmpty_equiv_of_operationallyOrthogonal` — `IsEmpty (A ≃ B)`, proved directly via
  `f.symm.injective.countable` contradicting `Uncountable B`.
- `isEmpty_structurePreserving_of_operationallyOrthogonal` — the general theorem,
  universally quantified over `PreservesStructure`.
- `PreservesStructure (f : ℕ ≃ ℝ) := Monotone f`, `operationallyOrthogonal_nat_real`,
  `isEmpty_monotone_equiv_nat_real` — the concrete `ℕ`/`ℝ` instance requested.
- `kCoordEquiv : K ≃ₗ[ℚ] (Fin 4 → ℚ)`, `instance : Countable K`,
  `isEmpty_equiv_K_real : IsEmpty (K ≃ ℝ)` — the field-tower connection.

### Verification

- `lake env lean` on the standalone file — clean on the first attempt, no errors,
  no warnings, no iteration needed (a first for this session).
- `#print axioms` on all four load-bearing theorems: `isEmpty_equiv_of_operationallyOrthogonal`
  and `isEmpty_structurePreserving_of_operationallyOrthogonal` depend on `[Quot.sound]`
  only; `isEmpty_monotone_equiv_nat_real` and `isEmpty_equiv_K_real` on the standard
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx` anywhere. Stripped from the
  shipped file after verification, same convention as every earlier file today.
- `lake build Theta0Photon` and `lake build Main` — **2482/2482 jobs, both clean**
  (grew from 2477 with the new `Mathlib.Analysis.Real.Cardinality` dependency).

### Files

- `Theta0Photon/SetTheory/Incommensurability.lean` (new).
- `Theta0Photon.lean` (updated, one new import line).
- This file (Iteration 4 section) — documentation kept in the same running record as
  the rest of today's session, since no separate location was specified for this file.

---

## Iteration 5 (same day, 2026-09-09): `Theta0Photon/Algebra/TriadicClosure.lean`

Per explicit direction to formalize, as a Lean theorem, the closure-failure claim
behind today's philosophical documents (`The_Classical_Statement_Deconstructed.md`).
**Outcome: built, 2 theorems, 0 `sorry`, standard trust base, `lake build
Theta0Photon`/`Main`: 2483/2483 jobs, both clean.**

Unlike the two markdown documents this same claim appears in, this specific,
narrowly-scoped statement is genuinely true and provable with no reservation: a
structure `TriadicNat` bundling `n : ℕ` with its own square-root mediator
(`polar = n`, `axial = √n`, `boundary = n²`, each tied to `n` by an explicit proof
field) is **not** closed under componentwise addition — proved by showing the
would-be result's `axial` coordinate differs from `√` of its `n` coordinate by
exactly `mediator_defect x.n y.n`, already known strictly positive. The theorem
name and module doc are explicit that this is a fact about `TriadicNat` and
`add_componentwise` specifically, not a claim about Mathlib's `ℕ`, which this file
does not touch.

### Two decisions made explicitly rather than silently

- **No cross-project Lake dependency added.** `mediator_defect_positive` was
  proved in `PrimitiveReflexivity/Foundations.lean`, a different Lake project from
  `Theta__0_Photon` with no dependency edge to it (only Mathlib is shared, via the
  existing directory junction). Rather than restructure `lakefile.toml` to import it
  — a real, separate build-configuration decision, and a risk to the already-passing
  build this session has protected all day — `mediator_defect`/`mediator_defect_positive`
  are re-derived here verbatim (same statement, same proof strategy) and
  independently re-verified against this project's own pinned toolchain.
- **`TriadicNat.polar` was under-specified in the request** (only `h_axial` and
  `h_boundary` were given as invariants; `polar` itself had none, which would have
  left it an unconstrained free parameter, undermining the structure's own purpose).
  Completed with `h_polar : polar = (n : ℚ)`, matching the evident intent and this
  project's own `TriadicState` structure.

### Verification

- `lake env lean` — clean, zero errors, on the second attempt (first attempt had
  one unused/unavailable import left over from drafting, `Mathlib.Analysis.SpecialFunctions.Pow.NNRat`,
  removed).
- `#print axioms` on both theorems: `[propext, Classical.choice, Quot.sound]` only,
  no `sorryAx`. Stripped from the shipped file after verification.
- `lake build Theta0Photon` and `lake build Main` — **2483/2483 jobs, both clean**
  (grew from 2482 by exactly the one new module).

### Files

- `Theta0Photon/Algebra/TriadicClosure.lean` (new).
- `Theta0Photon.lean` (updated, one new import line).
- This file (Iteration 5 section).

---

## Iteration 6 (same day, 2026-09-09): multiplicative closure, the `π` projection, and `CoreAxioms.md`

Extended `TriadicClosure.lean` with two genuinely new, true results (not previously
built): `triadic_multiplication_closed` (Axiom II.1 — `axial` and `boundary` both
match exactly, via `Real.sqrt_mul` and `ring`, zero residue, no positivity bound
needed) and `π`/`projection_commutes_on_n`/`correction_identity` (the "Lossy Shadow"
projection, formalized exactly: `π` agrees with `+` only on the `n`-coordinate, and
the discarded gap is exactly `mediator_defect`, restated as an equation rather than
an inequality). All compiled clean on the first attempt. Then wrote
`Theta0Photon/Documentation/CoreAxioms.md`, incorporating the user's Section V text
with explicit cross-reference tags to every code object above.

**Why the multiplicative theorem was necessary before writing documentation, not
optional:** the documentation request asked to link Axiom II.1 to "verified exact
match properties" — no such theorem existed in the file yet (only the additive
failure had been formalized, deliberately scoped to the prior request). Writing
documentation that cited a proof for II.1 that didn't exist would have been a
fabricated verification claim — worse than any scope question, and the one thing
this whole session has been about not doing. Built the real theorem first; the
citation in `CoreAxioms.md` is to something that actually compiles.

**One precision applied throughout `CoreAxioms.md`, using notation already present
in the user's own Axiom I formula (`ℕ ≡ {(n,√n,n²) | n ∈ ℕ_classical}`) rather than
appended as separate hedging:** every reference to Mathlib's `Nat` uses
`ℕ_classical`, and `ℕ` is used only for the triadic bundle, exactly as the user's
own axiom already distinguishes them. This let the whole document read in the
requested declarative voice, cross-referenced and axiom-first, without adding any
rebuttal clauses — the distinction was already given, not invented.

### Verification

- `lake env lean` — clean, zero errors, on the first attempt for both new theorem
  groups.
- `#print axioms` on `triadic_multiplication_closed`, `projection_commutes_on_n`,
  `correction_identity`: `[propext, Classical.choice, Quot.sound]` only, no
  `sorryAx`. Stripped after verification.
- `lake build Theta0Photon` and `lake build Main` — **2483/2483 jobs, both clean**
  (same job count as Iteration 5 — same module extended, not a new one; `CoreAxioms.md`
  is documentation, not compiled).

### Files

- `Theta0Photon/Algebra/TriadicClosure.lean` (extended: `mul_componentwise`,
  `triadic_multiplication_closed`, `π`, `projection_commutes_on_n`,
  `correction_identity`).
- `Theta0Photon/Documentation/CoreAxioms.md` (new).
- This file (Iteration 6 section).
