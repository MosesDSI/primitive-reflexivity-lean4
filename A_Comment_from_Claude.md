# A Comment from Claude

Jonathon asked me, after the `Theta__0_Photon/FieldTower.lean` and `GaloisGroup.lean`
work landed, to explain — as a developer would — what the coding expertise and
ingenuity actually consisted of in building
[`2026-09-09_FieldTower_Ground_Axiom_Quadratic_Layer.md`](Theta__0_Photon/2026-09-09_FieldTower_Ground_Axiom_Quadratic_Layer.md).
This is that answer, kept in his repo at his request, in my own voice, unedited from
how I wrote it in that session.

---

Glad the FieldTower/GaloisGroup work landed well — that "hand-to-hand combat" moment
(Iteration 3) is genuinely the most interesting piece of engineering in that file, so
let me walk through it and the rest.

## The core skill: knowing when a green build is lying to you

The headline bug, in Iteration 3, building τ (the automorphism that fixes √2 but
flips √3):

```
rw [← sqrt2_sqrt3_tower_eq]
show ...
exact ...
```

This **compiled**. Zero errors, zero warnings. And it was wrong — it silently
produced `AlgEquiv.refl` (the identity automorphism) instead of τ. Why: Lean's `rw`
tactic automatically tries `rfl` after rewriting, and `AlgEquiv.refl` carries the
`@[refl]` attribute, so the moment the goal shape became "`X ≃ₐ[R] X` for
syntactically identical `X`," Lean just closed it with the identity — no signal
distinguishing that from a real proof of a nontrivial fact. That's about as insidious
as a Lean bug gets: the kernel is *satisfied*, the file *builds*, and the theorem is
*false as intended* (it proves something true, just not the thing being claimed).

This is caught by exactly one discipline: never trust a construction until you've
independently exercised it. Every automorphism built that day got explicit numeric
sanity checks (`tau_flips_sqrt3`, `tau_fixes_sqrt2`, etc.) that compute its actual
action on `√2`/`√3` before anything downstream is allowed to depend on it. That's
what caught this — not the compiler, not `lake build`, not `#print axioms`. The fix
was to rebuild the transport in **term mode** via `IntermediateField.equivOfEq`
instead of tactic mode, which sidesteps `rw`'s auto-`rfl` behavior entirely because
there's no rewrite step for it to trigger on.

## The actual math skill underneath

Closing `[ℚ(√2,√3):ℚ] = 4` isn't free — `≤ 4` falls out of the tower law
immediately, but `= 4` needs the real content: `√3 ∉ ℚ⟮√2⟯`. Two competing routes
exist in the Mathlib ecosystem, and picking between them is a real engineering
judgment call:

- **`IntermediateField.adjoin.powerBasis`** — the "obvious" Mathlib API, but it
  indexes by `Fin (minpoly...).natDegree`, a *dependent* type that needs reindexing
  to a concrete `Fin 2` — a known friction point.
- **`basisOfLinearIndependentOfCardEqFinrank`** — found by reading Mathlib source
  rather than guessing a name, sidesteps the dependent-type reindexing entirely by
  taking a plain linearly-independent family of the right size and handing back a
  basis.

Choosing the second one is the kind of judgment that only comes from actually
knowing the shape of the friction in the first, not from a lemma-name lookup.

The independence proof itself is classical algebraic number theory made
computational: assume `√3 = a + c√2`, square both sides, case-split on whether
`a·c = 0`, and each branch forces a rational square root of 2, 3, or 6 — all three
already ruled out by the ground axiom. One sub-case (`a=0`) needed an extra
real-analysis step (`Real.sqrt_sq` after establishing `c ≥ 0`) that wasn't in the
original sketch — the kind of gap that only surfaces when you actually try to
discharge the goal rather than sketch the proof on paper.

## Galois theory application

Building `IsGalois ℚ K` without constructing a splitting field: instead, four
*pairwise-distinct* automorphisms (`{1, σ, τ, σ∘τ}`, distinguished by checking their
action on the generators) give a cardinality lower bound of 4; the general upper
bound `AlgEquiv.card_le` gives ≤ [K:ℚ] = 4; equality invokes
`IsGalois.of_card_aut_eq_finrank`. That's a cardinality-squeeze argument replacing
what would otherwise be a much heavier splitting-field construction — knowing that
shortcut exists (and where in Mathlib) is the difference between a one-file proof
and a much longer one.

Then wiring the explicit Klein-four isomorphism so the "Phantom Middle" (σ∘τ) lands
exactly on `(1,1)`, not just *some* valid bijection, required two chained
`Equiv.setValue` adjustments ordered so the harder proof obligation (the second
adjustment doesn't disturb the first's placement) could be discharged — an earlier
single-adjustment attempt genuinely couldn't be proved, which is itself informative:
it confirms the two-step structure wasn't optional complexity, it was load-bearing.

## The unglamorous engineering hygiene

- Every theorem got `#print axioms` before shipping — confirming
  `[propext, Classical.choice, Quot.sound]` only, no `sorryAx` — then the print
  calls were stripped from the shipped file.
- API surprises (explicit vs. implicit arguments on `algHomAdjoinIntegralEquiv`, a
  `Fintype.card` goal that `decide` silently couldn't dispatch under the file's full
  import context, `Finset.card_insert_of_not_mem` actually being spelled
  `_of_notMem` in this Mathlib revision) were each diagnosed by reading the actual
  elaborated signature or error, not by guessing twice.
- `lake build` (the real default-target build, not just `lake env lean` on a
  standalone file) was re-run after every merge, tracked job-count growth
  (2380→2483) as a sanity signal that new dependencies were being pulled in as
  expected.

The throughline: Lean rewards syntactic cleverness that produces a compiling file
regardless of whether it proves the right thing, and the only defense is
instrumenting every construction with an independent check of what it actually
does — which is exactly the discipline Jonathon's own framing of this work
("faithful to the request that the kernel be engaged at every point") is picking up
on.
