# A Comment from Claude

Jonathon asked me to explain, as a developer would, what the actual engineering
consisted of in extending
[`Theta0Photon/NavierStokes/ContinuumBridge.lean`](../Theta__0_Photon/Theta0Photon/NavierStokes/ContinuumBridge.lean)
with a finiteness lemma and then a composite bridge theorem — see the full
build summary at
[`Theta__0_Photon/2026-09-12_ContinuumBridge_Finite_SubHarmonic_Cutoff.md`](../Theta__0_Photon/2026-09-12_ContinuumBridge_Finite_SubHarmonic_Cutoff.md).
This is that answer, kept in his repo at his request, in my own voice, unedited
from how I wrote it in that session.

---

## The part that mattered: refusing to write a bridge that wasn't there

The request came in two stages. First: prove that only finitely many geometric
refinement levels stay above a resolution floor — a clean, self-contained
Archimedean-decay argument. Second, and more interesting: connect that
finiteness result *formally* to an existing theorem in the same file,
`discrete_lattice_prevents_gradient_blowup`, for a monograph.

The honest answer, before writing a single new line, was that the two theorems
didn't share a variable. `discrete_lattice_prevents_gradient_blowup`'s `h_min`
is a fixed abstract lattice's minimum spacing; the finiteness lemma's `h_min` is
a floor a *shrinking sequence* gets checked against — same symbol, two
different jobs. Writing monograph prose that said "formally proving X" over
that gap would have been the easy path and the wrong one. I said so directly,
asked which of two real options Jonathon wanted (a genuine new Lean theorem
bridging them, or accurate prose that names the gap instead of papering over
it), and only proceeded once the answer was "build the real theorem."

That's the actual engineering skill here, more than any single tactic: noticing
that a plausible-sounding request ("just link A to B") doesn't correspond to
anything provable yet, and stopping to say so instead of generating text that
looks like a proof.

## Building the bridge for real

The construction that came out of that conversation: `h_seq L₀ N` as a
first-class spacing term, `IsMaxValidLevel` naming *the greatest* valid
refinement level (not just "some" valid level — the finest grid that hasn't yet
dropped below the floor, which is the operationally interesting one),
`exists_isMaxValidLevel` producing that maximum as an actual computed term via
`Finset.max'` over the finite set the first lemma already proved exists, and
then two theorems: one instantiating the gradient bound at that computed
spacing, one showing that bound is in particular no worse than the plain
`h_min`-based one. `NodeSpace` stayed fully abstract throughout — I didn't
invent a concrete lattice model to make the composition "feel" more real; the
whole bridge runs through the derived scalar `h_seq L₀ N_max`, which is the
same generality the original theorem already had.

## Three bugs, all from compiling, none from re-reading

1. `push_neg` refused to run after `by_contra` on a `<` goal — *"made no
   progress."* Turned out `by_contra` had already normalized the negation to
   `≤` form itself in this Lean/Mathlib pin, so the textbook next step was
   redundant. `not_lt.mp` directly, instead.
2. My first draft of the `Fintype` corollary was a `noncomputable instance`
   with two ordinary hypotheses (`0 < L₀`, `0 < h_min`) as explicit arguments.
   Lean's answer: *"This instance has 2 arguments that cannot be inferred
   using typeclass synthesis"* — not a style nitpick, an outright rejection,
   because those aren't classes typeclass search can conjure. `def` instead of
   `instance`; same value, same call sites, just not auto-triggered (which was
   never going to happen anyway).
3. `h_seq`, unlike `ValidLevel` two declarations above it, needed
   `noncomputable` — *"depends on `Real.instDivInvMonoid`, which is
   noncomputable."* Same `Real.sqrt` arithmetic in both places; the
   `Prop`-valued one erases at compile time and the `ℝ`-valued one doesn't.
   Easy trap if you pattern-match on "the def right above this one compiled
   fine without the keyword."

## The discipline that kept this fast

Every lemma name here — `exists_pow_lt_of_lt_one`, `pow_le_pow_of_le_one`
(deliberately not its near-namesake `pow_le_pow_right_of_le_one'`, which lives
one file over with a different hypothesis shape and doesn't fire here),
`lt_div_iff₀`, `Set.finite_lt_nat`, `Finset.max'`/`.max'_mem`/`.le_max'` — came
from grepping this project's actual pinned Mathlib checkout under
`.lake/packages/mathlib`, not from recalling a name and hoping it survived
however many refactors since whatever version I last saw it in training. That's
the difference between one clean build after fixing three real logic bugs, and
a long tail of `unknown identifier` errors chasing lemma names that moved or
never existed the way I remembered them.

## Where it stands

`lake build Theta0Photon` and `lake build Main` both clean, 2627/2627.
`#print axioms` on every new declaration: standard trust base only
(`propext`, `Classical.choice`, `Quot.sound`), zero `sorry`. Committed locally.
Whether this and the prior session's commit get pushed is a live question I
raised rather than settled myself — see the build summary's closing note.
