# A Comment from Claude

Jonathon gave me a fully specified module this time — exact def names, exact
theorem statements, even the intended proof tactic for each one — and asked me
to add it to the project. See the full build summary at
[`Discrete/2026-09-14_HarmonicCenter_Formalization.md`](../Discrete/2026-09-14_HarmonicCenter_Formalization.md).
This is that answer, kept in his repo at his request, in my own voice, unedited
from how I wrote it in that session.

---

## When the spec is precise, the job is verifying the one place it isn't

Everything here — `omega`, the symmetry lemma, the three residue classes, the
distance sums — was specified down to the exact values (`distSum 11 C2 = 36`,
not "some smaller number"). I checked the arithmetic by hand before writing
any Lean: mod-3 residue classes of `{1,...,21}` do put `11` in the class
`n % 3 = 2`, and summing `|c - 11|` over each class does give `37, 36, 37`.
That's real confirmation the spec is internally consistent, not just a
type-checking exercise — if the numbers hadn't matched, no tactic choice would
have saved it.

Three of the four proofs went through with the exact tactic named in the spec,
first try: `ring` + `abs_neg` for the symmetry lemma, `decide` for set
membership. The fourth — summing over a filtered `Finset.Icc` — was specified
as `norm_num`, and that's the one place the spec's proof strategy didn't match
what the tactic actually does. `norm_num` normalizes numerals and closes
numeral (in)equalities; it doesn't know how to unfold a `Finset.sum` over a
`LocallyFiniteOrder`-generated `Finset.Icc` into 21 individual terms it could
then add up. Run as specified, it left the goal exactly where it started —
an unevaluated big-operator sum with a filter predicate inside it, dressed up
as if progress had been made. I didn't push harder on `norm_num` with a longer
simp-lemma list to force it through; the goal is a fully concrete, finite,
decidable proposition, which is precisely what `decide` is for — and it's the
same tactic the spec itself already reached for one theorem earlier in the
same file. Using it here isn't a downgrade in rigor, it's using the tool built
for this exact shape of goal instead of the one that happens to share a
name with the phrase "compute the numbers."

## Why I didn't just report success

The instructions asked specifically for `norm_num`, by name, so getting a
"clean build" by quietly substituting a different tactic and not saying so
would have answered a different question than the one asked. The honest
report is: the spec's four proof strategies as written, one of them doesn't
compile as specified, and here's exactly why and what does instead — same
discipline as every other build in this project, compile first, then describe
what actually happened.

## Where it stands

`lake build PrimitiveReflexivity.Discrete.HarmonicCenter`: 930/930, clean.
`#print axioms`: `harmonic_distance_symmetry` needs only `propext` (pure
algebra, no choice or quotient dependency); the other two sit at the standard
`[propext, Classical.choice, Quot.sound]`. Zero `sorryAx` throughout. Wired
into the root import list; full-project rebuild afterward: 2747/2747, no
regressions. Committed and pushed.
