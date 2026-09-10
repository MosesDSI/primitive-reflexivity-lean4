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

---

## Shortcuts and pitfalls for other Lean4/Mathlib coders

Jonathon asked afterward whether any of this would actually help visitors — people
navigating Lean4/Mathlib's density for their own projects, not just reading about
this one. Here's that answer, kept as raw as I wrote it:

Genuinely, yes — a few things from this build generalize well beyond this specific
proof, the kind of thing that would've saved real time if I'd known them going in.
Here's what I'd actually pull out as reusable lessons for someone navigating
Lean4/Mathlib's density:

**1. When you're building an `Equiv`/`AlgEquiv` via tactics, don't trust a green
build — sanity-check the direction.** This is the biggest one. `rw` and several
other tactics auto-try `rfl` afterward, and anything tagged `@[refl]` (like
`AlgEquiv.refl`) will silently swallow a goal that happens to reduce to "X ≃ X" —
even when you meant to construct a *specific nontrivial* equivalence. The compiler
gives you nothing: no warning, no error. The generalizable habit: any time you build
an isomorphism/equivalence by tactic manipulation rather than an explicit term,
write one extra line that computes what it actually does on a concrete input and
check that against what you intended.

**2. `show` is an underused tool for "there's no lemma for this."** When I needed
`finrank ℚ ↥(E.restrictScalars ℚ) = finrank ℚ ↥E` and no named Mathlib lemma
existed for it, `show` (which only succeeds if the new goal is *definitionally*
equal to the old one) confirmed the two sides were already the same thing under the
hood — no lemma needed. Worth trying before spending time hunting Mathlib for a
bridging lemma that may not exist because it doesn't need to.

**3. Read Mathlib's source instead of guessing lemma names.**
`basisOfLinearIndependentOfCardEqFinrank` (avoids a dependent-type reindexing
headache) and `Module.Dual.finrank_ker_add_one_of_ne_zero` (the general
rank-nullity theorem) were both found by opening the actual source file, not by
autocomplete-guessing a plausible name. Mathlib's naming conventions are consistent
enough to guess *close*, but "close" fails to compile — actually reading the file
that defines the thing you need is often faster than three wrong guesses.

**4. `#check @lemma` before applying anything with more than one argument.**
Several lemmas here had a base field as an *explicit* first argument even though it
reads naturally as something Lean should infer. `#check @lemma_name` shows the
real elaborated signature before you burn a cycle on a misapplied argument.

**5. `decide` doesn't work over `ℝ`.** The kernel can't evaluate real numbers
computationally — `decide` on any goal involving real-number equality just fails or
hangs. `norm_num`/`nlinarith` are the right tools there; this trips people up
because `decide` works fine for `ℕ`/`Fin n` and the failure mode isn't always an
obvious error message.

**6. If an error cascade looks unrelated to what you just typed, suspect
`autoImplicit`.** An unqualified name Lean doesn't recognize can silently become an
implicit universe-polymorphic type variable instead of throwing "unknown
identifier" — producing a pile of confusing downstream errors that look like
they're about something else entirely.

I think this helps visitors more than the narrower "what I personally built"
framing of the rest of this doc — it's the kind of thing someone hits on their own
first nontrivial Mathlib project and has no way to know in advance.
