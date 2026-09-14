# A Comment from Claude

Jonathon handed me a self-contained draft — square boundary unfolded into a line
segment, four theorems about it — and asked me to verify it against real Lean 4
and Mathlib, not just read it and say it looked right. See the full build summary
at
[`Geometry/2026-09-14_SquareUnfolding_Formalization.md`](../Geometry/2026-09-14_SquareUnfolding_Formalization.md).
This is that answer, kept in his repo at his request, in my own voice, unedited
from how I wrote it in that session.

---

## It didn't compile. That's the finding.

The draft looked reasonable on a read-through — four small geometric lemmas, each
with a short tactic proof. It failed to build on the first try, and on the
second. Both failures were real, not typos.

**First pass:** every `linarith` and `ring` call errored with "unknown tactic."
The draft's two imports (`Mathlib.Data.Real.Basic`,
`Mathlib.Algebra.Order.Ring.Defs`) don't transitively pull in either tactic's
extension at this project's pinned Mathlib revision. A narrow, targeted-looking
import list is not the same thing as a sufficient one — I added
`Mathlib.Tactic.Linarith` and `Mathlib.Tactic.Ring` explicitly rather than
reaching for a blanket `import Mathlib.Tactic`, since the file genuinely only
needs those two.

**Second pass, the more interesting bug:** three of the four boundary-edge cases
started passing, and one — the `left` edge, index `3` — kept failing with
`linarith failed to find a contradiction` and `ring` bailing out to `ring_nf`
with a goal like `s * 3 = s * ↑↑3` still open. The index type was `Fin 4`, and
`edgeOffset` cast `.val` of that `Fin 4` element straight to `ℝ`. `dsimp` unfolds
the *definition* (which edge maps to which literal) but does nothing to reduce
`Fin.val` of the resulting numeral — so the goal carried `↑0 * s`, `↑1 * s`,
`↑↑3 * s` as literally opaque terms to both tactics, not as `0`, `s`, `3*s`. Why
did `0`, `1`, `2` clear and `3` didn't? I don't have a fully satisfying answer —
some combination of which `Fin.val` simp lemmas fire for which literals at this
Mathlib pin — and I didn't chase it further once I saw the actual fix, which
made the question moot rather than answered: **the file never uses `Fin 4`'s
bounded or modular structure at all.** It's cast to `ℝ` on its very next use and
never touched again. Swapping `SquareEdge.index : SquareEdge → Fin 4` for
`SquareEdge.index : SquareEdge → ℕ` removes the cast-reduction fight entirely —
`Nat.cast` of a literal is exactly the kind of term `ring` is built to normalize
— and it's a strictly simpler type for what the function actually does. Fixing
the bug and simplifying the design turned out to be the same edit.

## What I didn't do

I didn't paper over the `left`-case failure with a bigger hammer (`decide`,
`omega`, a `simp` with a longer arbitrary lemma list) while leaving `Fin 4` in
place. That would have "worked" in the sense of closing the goal, but it would
have hidden the actual mismatch — a type carrying unused structure — behind
tactic firepower instead of removing it. The version that shipped has no lemma
list longer than three names in any proof.

## Where it stands

`lake build PrimitiveReflexivity.Geometry.SquareUnfolding`: 853/853, clean.
`#print axioms` on all four theorems: `[propext, Classical.choice, Quot.sound]`,
zero `sorryAx`. Wired into the root `PrimitiveReflexivity.lean` import list;
full-project rebuild afterward: 2746/2746, no regressions in the two
pre-existing files. Committed and pushed.
