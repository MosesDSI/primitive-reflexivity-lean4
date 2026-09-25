# Addendum to "An Order-Theoretic Obstruction to Rational Retraction"

**Status:** Sections 9.2–9.3 of the companion PDF (`Order_Obstruction_Technical_Paper.pdf`) are
superseded by this addendum as of commit `f8fec74`. This file is a plain-text update, not a
replacement typeset source — **no LaTeX, typst, or Markdown source for the PDF exists in this
repository**; only the compiled PDF itself is present, and it is untracked in git. If the PDF is
regenerated later, Sections 9.2–9.3 below are the text to fold back in.

---

## 9.2 (superseding). Current State of QS — Complete

`QS` is a certified ordered field. All six roadmap steps below are proved, kernel-checked, and
part of this project's own `lake build` (no longer standalone). Verification facts, checked
directly rather than assumed:

- **Commit:** `f8fec74` (`feat(QS): complete density and link OrderObstruction to main build`),
  on top of `c9dea0e` (field laws / order) and `b6eabc2` (additive structure / inverse).
- **File:** `PrimitiveReflexivity/Discrete/OrderObstruction.lean` — moved into the library tree
  this session; previously stood alone at the repo root, outside `lake build`.
- **Lake integration:** `lake build` → **2748/2748 jobs, "Build completed successfully."**
  (Re-confirmed by direct kernel re-check on 2026-09-25, independent of the cached lake result.)
- **Declaration count:** 90 top-level declarations (81 `theorem`, 9 `def`) in the file.
- **Axiom footprint:** every declaration with a nontrivial proof checked via `#print axioms`
  (64 such checks recorded in the file) lands at exactly `[propext, Classical.choice,
  Quot.sound]` — Lean's own standard trust base, nothing added.
- **`sorryAx`:** zero, confirmed both by the `#print axioms` output (which would list `sorryAx`
  if present) and by a direct text scan of the file.
- **Escape hatches** (`sorry`, `native_decide`, user `axiom`, `unsafe`, `implemented_by`): zero,
  confirmed by scan across all 27 tracked `.lean` files in this repository, not just this one.
- **Independent kernel replay:** compiled to a fresh `.olean` and re-checked via `leanchecker`
  (a checker independent of the elaborator that produced the proof) — clean exit. A negative
  control (pointing `leanchecker` at a path where the module can't be found) was run first and
  confirmed to fail, so the clean exit on the real run is a genuine replay, not a silent no-op.

## 9.3 (superseding). Roadmap — All Steps Complete

| Step | Content | Status |
|---|---|---|
| 1. Additive structure | `(a+b√2)+(c+d√2)=(a+c)+(b+d)√2`; negation and zero componentwise | **Done** — `b6eabc2` |
| 2. Inverse | `1/(a+b√2)=(a-b√2)/(a²-2b²)` | **Done** — `b6eabc2` |
| 3. Field laws | Associativity, commutativity, distributivity, identities, inverses | **Done** — `c9dea0e` |
| 4. Total order | Trichotomy and transitivity for all elements | **Done** — `c9dea0e` |
| 5. Compatibility | Order respects addition; positives closed under multiplication | **Done** — `c9dea0e` |
| 6. Density and Archimedean property | A rational between any two elements; no infinitesimals | **Done** — `f8fec74` |

Two of these steps turned out to need substantially more than the table's one-line gloss
promised, and both are worth recording precisely, since a kernel-verified theorem certifies
exactly its formal statement — the *route* to that statement is not otherwise visible.

### 9.3.1 Step 4's real content: transitivity needs closure under addition, not just norm sign

Trichotomy (deciding the sign of one element) genuinely is decided by comparing that element's
own two rational components against each other, as the roadmap states. Transitivity is a
different claim: it reduces to `Pos x → Pos y → Pos (x + y)` — positivity closed under addition —
and the norm `N(x) = a² - 2b²` is **not** additive, so norm sign alone does not decide it. The
hard case is two summands dominant in *opposite* directions (one via its rational part, one via
its `√2` part): no rational bound found by squaring one inequality at a time closes it.

The resolution rests on two pure polynomial identities, provable by clearing denominators and
verified directly by the kernel with no approximation and no `√2` term ever written:

```
V·(U - A) - A·(B - V) = U·V - A·B
B·(U - A) - U·(B - V) = U·V - A·B
```

where a summand `U - B√2` is a-dominant (`U² > 2B²`) and a summand `-A + V√2` is b-dominant
(`A² < 2V²`). `U·V > A·B` follows from `U²V² - A²B² = (U²-2B²)·V² + (2V²-A²)·B² > 0` (both terms
strictly positive), and each identity above converts one branch of "the sum's negation is
positive" into a direct contradiction with the summand's own dominance inequality, via squaring
an inequality between two already-nonnegative quantities. See `mixed_not_neg` and
`dominance_mul_lt` in `OrderObstruction.lean`, and
`2026-09-24_OrderObstruction_QS_Field_Order_Complete.md` for the full derivation, including three
real bugs the kernel caught mid-draft that are not visible from the final proof text.

### 9.3.2 Step 6's real content: density needs a quantitative rate of convergence, not a midpoint

The roadmap's own gloss — "generalization of the step map" — was the accurate part of the
description; a plainer reading ("leverage the existing rational-vs-√2 comparison lemmas, use a
midpoint") undersells it. Those lemmas (`below_s`, `above_s`) only compare a rational against the
*fixed* point `s = √2`. Density between two **arbitrary** elements of `QS` needs a rational
strictly inside a gap that can be arbitrarily small while both endpoints carry arbitrarily large
irrational offsets — concretely, `x = 0.0001 + 1000000·√2` and `y = 0.0002 + 1000000·√2` differ by
a rational `0.0001`, yet no rational sits between them without knowing `√2` to roughly nine
correct decimal digits. This is a genuine constructive Diophantine-approximation result, not a
corollary of the order structure already built.

The development, entirely new this session (`f8fec74`):

- **A quantitative halving rate** for the existing `step` map's approach to `√2`. The prior,
  qualitative `step_below`/`step_above` show the iterate moves *closer*; `step_gap_half` and
  `step_gap_half_above` show the squared gap `2 - r²` (or `r² - 2`) at least **halves** every
  iteration, via the algebraic identity `2 - step(r)² = 2·(2-r²)/(r+2)²` combined with
  `(r+2)² > 4` whenever `r > 0`.
- **Two convergent sequences** (`approxLo`, `approxHi`, iterating `step` from `1` and `2`
  respectively) with proven two-sided bounds — `approxLo_gap : 2 - approxLo(n)² ≤ (1/2)ⁿ`,
  `approxHi_gap : approxHi(n)² - 2 ≤ 2·(1/2)ⁿ` (the asymmetric constant reflects the two
  sequences' different starting distances from `2`).
- **An Archimedean fact for `Rat`** (`archimedean : ∀ δ > 0, ∃ n, 1 < δ·2ⁿ`), built from raw
  `Nat`/`Int`/`Rat` numerator-denominator arithmetic, with no Mathlib available.
- **`approx_sandwich`**: given any rational `b` and margin `ε > 0`, produces a rational `t` with
  `t` on the correct side of `b·√2` and within `ε` of it — the general-purpose approximation
  engine, built once and reused.
- **`pos_margin`**: given any positive element of `QS`, produces an explicit *positive rational*
  lower bound on it — i.e., a concrete witness that a positivity gap has positive rational size,
  not merely positive `QS`-size. The two dominance branches need genuinely different closed-form
  certificates (not mirror images of one another): the a-dominant case uses
  `ε = (a²-2b²)/(2a)`, verified via the identity `(a²+2b²)² - 2b²(2a)² = (a²-2b²)²`; the
  b-dominant case uses `ε = (2b²-a²)/(4b)`, verified via
  `(a+4b)² - 2b² = (2b²-a²) + 2(a+2b)² + 4b²` and
  `32b⁴ - N² = (2b²-a²)·((a+4b)²-2b²)`. The natural "mirror" of the first formula for the second
  case gives the wrong inequality direction — found to be wrong by testing concrete numbers
  before attempting a proof, not by a failed proof attempt.
- **`qs_dense`** chains `pos_margin` (get a rational-sized gap) → `approx_sandwich` (sandwich the
  lower endpoint's irrational coefficient to within that gap) → `pos_add` (already proved in
  `c9dea0e`) — the same "restate as a raw `Pos` tuple, add, `grind` the resulting rational
  identity" technique `transitivity` already used, so the final assembly closed on the first
  attempt once the analytic pieces were in hand.

### 9.3.3 The capstone theorem

```
theorem incommensurability_blocks_retraction :
    ¬ ∃ f : QS → Rat, (∀ x y, x < y → f x ≤ f y) ∧ (∀ q, f (emb q) = q) :=
  no_order_retraction_Qsqrt2
```

A direct restatement of `no_order_retraction_Qsqrt2` (already proved, from the original session's
work), now sitting alongside a fully certified ordered field rather than a bare witness
construction — the thesis's central claim (no order-preserving retraction of an incommensurable
extension back onto ℚ) applied to a number system whose own field and order laws are themselves
kernel-checked from first principles, inside the bare-Lean trust base, start to finish.
