# Build Summary — QS Field Laws, Global Trichotomy, Transitivity, Order Compatibility (Roadmap Steps 3–5)

**Date:** 2026-09-24
**File:** `OrderObstruction.lean` (bare Lean 4, no Mathlib; standalone, per prior session's finding)
**Objective:** Complete Section 9.3's roadmap Steps 3 (field laws), 4 (total order), and 5 (order/arithmetic compatibility), building on the additive/inverse structure from commit `b6eabc2`.

---

## 1. What turned out to be genuinely hard

The roadmap table describes Step 4 as "Norm sign decides every comparison; Proposition 1.1 excludes ties" — accurate for **trichotomy** (deciding the sign of a single element), but **transitivity** needs more: it reduces to "`Pos x → Pos y → Pos (x + y)`" (positivity closed under addition), and that fact does *not* follow from norm signs alone. A rational a-dominant positive number (`x.a² > 2x.b²`) and a rational b-dominant positive number (`x.a² < 2x.b²`) can sum to either kind, and which one depends on the actual magnitudes, not just which of `x.a`, `x.b` "wins" in each summand individually. This is real algebra, not busywork — proving it is equivalent to proving ℚ(√2)'s positive cone is closed under addition, using only rational arithmetic (no `Real.sqrt`, since this file has no Mathlib).

**The resolution (`mixed_not_neg`, `dominance_mul_lt`):** for two positive summands dominant in *opposite* directions (`U, -B` from one, `-A, V` from the other, with `U²>2B²` and `A²<2V²`), two pure polynomial identities settle it without ever introducing an irrational quantity:
```
V*(U-A) - A*(B-V) = U*V - A*B
B*(U-A) - U*(B-V) = U*V - A*B
```
`U*V > A*B` follows from `U²V² - A²B² = (U²-2B²)*V² + (2V²-A²)*B² > 0` (both terms positive). Each identity then converts one branch of "the sum's negation is positive" into a contradiction with the summand's own dominance inequality, via squaring an inequality between two already-nonnegative quantities. No case is left needing an approximation to √2 — every step is exact rational algebra.

The user relayed a `sqLe_add`/`le_of_sq_le` snippet mid-session for the *same-direction* dominance case (both summands a-dominant, or both b-dominant) — verified, fixed two lemma-name issues (`Rat.le_total`/`Rat.le_iff_lt_or_eq` need named/explicit arguments; `Rat.lt_of_le_of_lt`/`Rat.le_of_eq` don't exist in this core, replaced with `grind`), and it slotted in directly.

## 2. What turned out to be easier than feared

Multiplication (`mul_pos`) looked like it might need the same opposite-dominance machinery a second time. It doesn't: `x = emb x.a + emb x.b * s` decomposes any branch1 (nonnegative-pair) factor into a positive-rational-scaled term plus a positive-rational-scaled-times-`s` term, and both `pos_scale` (scaling by a positive rational) and `pos_s_mul` (multiplying by `s` alone) preserve positivity with **no** dominance ambiguity — multiplying by `s = 0+1√2` turns out to just swap-and-double a branch's components, mapping branch2↔branch3 with the needed inequality being exactly the hypothesis already in hand. `pos_add` (already proven) finishes the sum. The remaining branch2/branch3 combinations for multiplication have components with an *unconditional* sign (e.g. two a-dominant positives always multiply to an a-dominant positive, checkable by direct computation), with `norm_mul` (`norm(x*y) = norm x * norm y`, a clean ring identity) supplying the needed square inequality from the sign of `norm x * norm y`. Zero dominance casework needed for multiplication at all.

## 3. Real bugs the kernel caught mid-draft (not hypothetical)

- **Wrong disjunct in `pos_add_branch1_left`:** claimed `0 < sum.b` when only `0 ≤ sum.b` was available (the boundary `sum.b = 0` is real and reachable) — should have claimed `0 < sum.a` instead, which *is* unconditionally true there. Caught because `grind` couldn't prove the false claim.
- **Overlapping case split:** `Rat.le_total` splits into two `≤` branches that share the boundary point; using it to route into `Pos`'s *strict* branch2/branch3 conditions left the boundary case (`sum.a = 0` exactly) asking to prove a strict inequality from only a non-strict hypothesis. Fixed by switching to `rat_trich` (a genuine 3-way `<`/`=`/`>` split) and folding the equality case into branch1.
- **`sqLe_add2` called with the wrong sign:** for branch3+branch3, `x.a < 0` violates `sqLe_add2`'s `0 ≤ p₁` requirement directly — needed `-x.a`, not `x.a`, as the argument.
- **`pos_scale`'s opening `show` wasn't actually defeq:** `q*y.a + 2*(0*y.b)` doesn't reduce to `q*y.a` by computation alone (`0*y.b = 0` is a ring *fact*, not a definitional unfold, for an abstract `Rat` variable) — fixed by keeping the `show` target in the raw, unsimplified form the `Mul` instance actually produces.
- **Bare `grind` calls failing on two-variable product signs** (e.g. `0 < x.a * y.a` from `0 < x.a, 0 < y.a`) throughout `mul_pos`: `grind`'s ring normalization does not by itself derive order facts about products of two independent variables — every one needed an explicit `Rat.mul_pos`/`Rat.mul_nonneg` call supplied as a hint (confirmed empirically: `grind` handled *linear*-coefficient products like `0*y.a` fine, but not genuine two-variable sign multiplication). One of these (`branch3+branch2`'s `hsb`) had an outright wrong target sign in an early draft (`x.a*y.b < 0` claimed where the true sign is positive, `x.a<0` and `y.b<0`) — caught by the kernel rejecting the mismatched final `refine`, not by re-reading.
- **`Classical.byContradiction`, not `by_contra`/`push_neg`:** neither tactic exists in this bare-Lean environment; `Classical.byContradiction` (core, backed by the `Classical.choice` axiom already in this file's footprint) does the same job.

## 4. Verification

- `lean OrderObstruction.lean` (v4.33.1, the project's actual pinned toolchain — see the prior session's note that the paper's stated 4.34.1 doesn't exist in this environment): 0 errors.
- `#print axioms` on all 24 new declarations (`mul_assoc`, `mul_comm`, `one_mul`, `mul_one`, `left_distrib`, `right_distrib`, `add_lt_add_left`, `pos_trichotomy`, `trichotomy`, `transitivity`, `sq_le_sq_of_nonneg`, `sq_lt_sq_of_nonneg`, `le_of_sq_le`, `sqLe_add`, `sqLe_add2`, `dominance_mul_lt`, `mixed_not_neg`, `pos_add_branch1_left`, `pos_add`, `norm_mul`, `pos_scale`, `pos_s_mul`, `pos_mul_branch1_left`, `mul_pos`): every one lands at `[propext, Classical.choice, Quot.sound]`, the file's existing standard trust base. Zero `sorryAx`.
- Escape-hatch scan (`sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `by_contra`): no matches.
- Independent kernel replay: compiled to a fresh `.olean`, ran `leanchecker` against it — clean exit, both against the scratch draft and again against the actual committed file after the diff was applied (a negative control confirming `leanchecker` genuinely fails on a missing module was already established in the prior session and re-used here).

## 5. Git

Committed to `PrimitiveReflexivity` (`origin` = `github.com/MosesDSI/primitive-reflexivity-lean4`) and pushed, per the repo's standing Category B (engineering-report) rule. Staged exactly: `OrderObstruction.lean`, this file, and the companion `A_Comment_from_Claude/` entry + README index update.
