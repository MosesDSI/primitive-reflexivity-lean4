# Build Summary — QS Density, Capstone Theorem, and Lake Integration (Roadmap Step 6 + Final Wiring)

**Date:** 2026-09-24
**File:** `PrimitiveReflexivity/Discrete/OrderObstruction.lean` (moved from repo root this session — see §4)
**Objective:** Complete Section 9.3's final roadmap step (density/Archimedean), state the capstone incommensurability theorem, and wire the file into `lake build` for the first time.

---

## 1. What the task's own hint undersold, again

The task described density as "leverage `below_s`/`above_s`, use the rational midpoint on component projections." That undersells it the same way "norm sign decides transitivity" undersold the additive-closure work two sessions ago. `below_s`/`above_s` only compare a rational against the *fixed* point `s = √2`; `qs_dense` needs a rational strictly between **two arbitrary** `QS` elements, whose gap can be arbitrarily small while both elements carry arbitrarily large irrational offsets (concretely: `x = 0.0001 + 1000000·√2`, `y = 0.0002 + 1000000·√2` — finding a rational between these needs `√2` known to about 9 correct decimal digits, not a "midpoint"). This is genuinely a constructive Diophantine-approximation result, not a corollary of what was already built. The roadmap table's own one-line gloss ("Generalization of the step map") was the accurate part — I ended up doing exactly that, at real quantitative cost.

## 2. What had to be built from scratch

- **`step_gap_half` / `step_gap_half_above`**: the qualitative `step_below`/`step_above` (already in the file) show the iterate moves closer to `√2`; they say nothing about *how much* closer. Derived the exact rate algebraically: `2 - step(r)² = 2·(2-r²)/(r+2)²`, and since `r>0 ⟹ (r+2)²>4`, the squared gap **at least halves** every iteration. The forward algebra is degree-4 in `r` and `grind` can't discover the needed factorization on its own — it closes once handed the explicit identity `(2-r²)(r+2)² - [4(r+2)²-2(2r+2)²] = r(r+4)(2-r²)`, a product of three positive terms.
- **`approxLo`/`approxHi`**: two explicit `Nat → Rat` sequences (from `1` and `2` respectively) iterating `step`, each proven to stay on the correct side of `√2` (`approxLo_bound`/`approxHi_bound`) and to close the gap geometrically (`approxLo_gap`/`approxHi_gap`, `≤ (1/2)ⁿ` and `≤ 2·(1/2)ⁿ` — the two sequences start at different distances from 2, so the bounds aren't symmetric; missing this cost one failed compile at `n=0`).
- **`archimedean`**: `∀ δ>0, ∃n, 1 < δ·2ⁿ` — built from scratch via `2ⁿ ≥ n+1` (induction) and `δ·δ.den = δ.num` (`rat_num_den`, itself needing `Rat.divInt`/`Rat.div_mul_cancel` plumbing since the `/.` notation isn't in scope without `open Rat`).
- **`approx_sandwich`**: given `b : Rat` and a target margin `ε>0`, produces `t` with `Pos⟨t,-b⟩ ∧ Pos⟨ε-t,b⟩` — i.e. a rational `t` on the correct side of `b·√2` and within `ε` of it. Three cases (`b<0`, `b=0`, `b>0`); the `b>0` case needs an extra case split (`t≤ε` is free via branch1; `t>ε` needs the real precision argument) that the `b<0` case doesn't, because of which branch of `Pos` each falls into.
- **`pos_margin`**: given `Pos z`, produces an explicit *positive rational* `ε` with `emb ε < z` — i.e. a concrete witness that the gap has positive rational size, not just positive QS-size. Branch1 is direct (`z.a/2` or a symmetric construction). Branch2's closed form `ε = (a²-2b²)/(2a)` was found by solving for the exact value that makes a difference-of-squares identity `(a²+2b²)² - 2b²(2a)² = (a²-2b²)²` close by itself. Branch3's analogous problem (`ε = (2b²-a²)/(4b)`) needed a *different* certificate — the natural mirror of branch2's formula gives the wrong inequality direction, discovered by testing concrete numbers before the algebra, not after. The working certificate: `(a+4b)² - 2b² = (2b²-a²) + 2(a+2b)² + 4b²`, then `32b⁴ - N² = (2b²-a²)·((a+4b)²-2b²)` links it back to the actual squared target — both found by polynomial division, not guessed.
- **`qs_dense`**: chains `pos_margin` (get a rational gap `ε`) → `approx_sandwich` (sandwich `x.b` to within `ε`) → `pos_add` (already proved, two sessions ago) to show `x < emb(x.a+t) < y`, using exactly the same "restate the goal as a raw `Pos` tuple, `pos_add` the pieces, `grind` the resulting rational identity" technique that `transitivity` used — once the hard analytic work was in hand, the final assembly compiled on the first try.
- **`incommensurability_blocks_retraction`**: the literal one-line capstone the task asked for — `no_order_retraction_Qsqrt2` already has exactly this type, so it's a direct alias.

## 3. Recurring `grind` failure mode, confirmed again

Every real compile failure in this session was the same shape already documented in the prior two sessions' notes: `grind` cannot derive an order fact about a **product of two independent variables** (`0 < q·y.a` from `0<q, 0<y.a`; `0 < b*b` from `b≠0`) purely from ring normalization — it needs an explicit `Rat.mul_pos`/`Rat.mul_nonneg` (or a purpose-built helper like the new `sq_pos_of_ne`, `neg_pos_iff`, `div_pos_of_pos_of_pos`) supplied as a hint, even when the needed fact is "obviously" in scope. When several such hypotheses pile up in one proof, `grind`'s own diagnostic dump shows it exploring nonsensical case splits (e.g. `eps = approxLo n`) rather than failing cleanly — a signal to isolate the step with an explicit `have`, not to add more context and retry.

## 4. Lake integration

`OrderObstruction.lean` lived at the repo root since its first session, explicitly flagged as "standalone, not `lake build`-checked" in that session's own Limitations section. Moved (`git mv`, not copied) to `PrimitiveReflexivity/Discrete/OrderObstruction.lean`, matching the layout of every other module in the library, and added `import PrimitiveReflexivity.Discrete.OrderObstruction` to the root `PrimitiveReflexivity.lean`. `lake build`: **2748/2748 jobs, "Build completed successfully."** The file imports nothing from Mathlib (this project's `mathlib` dependency is available to the build but untouched by this file), so the axiom footprint is unaffected by being pulled into the Mathlib-backed project — every `#print axioms` line in the build log still reports the same `[propext, Classical.choice, Quot.sound]` base as the standalone `lean`/`leanchecker` runs below.

## 5. Verification

- `lean OrderObstruction.lean` (standalone, v4.33.1, matching prior sessions): 0 errors.
- `#print axioms` on all 18 new declarations from this session (`rat_num_den`, `two_pow_ge`, `archimedean`, `step_gap_half`, `step_gap_half_above`, `approxLo_bound`, `approxHi_bound`, `approxLo_gap`, `approxHi_gap`, `rat_mul_pow`, `rat_one_pow`, `neg_pos_iff`, `sq_pos_of_ne`, `div_pos_of_pos_of_pos`, `approx_sandwich`, `pos_margin`, `qs_dense`, `incommensurability_blocks_retraction`): every one lands at `[propext, Classical.choice, Quot.sound]`. Zero `sorryAx`.
- Escape-hatch scan (`sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `by_contra`): no matches.
- Independent kernel replay: compiled to a fresh `.olean`, ran `leanchecker` against the standalone file — clean exit — before applying the diff to the committed file, then re-ran both the direct `lean` compile and the `leanchecker` replay against the actual committed file a second time. Then `lake build` from the project root, a third independent build path (its own toolchain resolution, its own `.olean` cache), also clean.

## 6. Git

Committed to `PrimitiveReflexivity` (`origin` = `github.com/MosesDSI/primitive-reflexivity-lean4`) and pushed, per the repo's standing Category B (engineering-report) rule. Staged exactly: the moved `OrderObstruction.lean` (as a rename, not delete+add), `PrimitiveReflexivity.lean` (import wiring), this file, and the companion `A_Comment_from_Claude/` entry + README index update.
