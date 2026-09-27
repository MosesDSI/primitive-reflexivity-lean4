# PhantomFixedField Proof Pass

**Date:** 2026-09-27
**Project:** `PrimitiveReflexivity/Theta__0_Photon` (subproject `Theta0Photon`)
**Toolchain:** `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (pinned)
**File:** `Theta0Photon/Theta0Photon/Algebra/PhantomFixedField.lean`

## Objective

A target statement file (`PhantomFixedField.lean`) was drafted outside the
repo (Opus 5.5, claude.ai browser) as a proof assignment: eight theorems
about `K = ℚ(√2, √3)`'s "Phantom Middle" automorphism `π = σ∘τ`, stated with
`sorry` in place of proofs, plus rules ("don't change statement content, no
new axiom/sorry/native_decide, keep `#print axioms` to the standard three").
The user asked for a review of the drafted target before building it.

## Review verdict

Agreed with the mathematical content as drafted — all four claims (A: `π`
fixes `√2·√3`, `σ`/`τ` negate it; B: exactly `{1,π}` fix it; D: `fixedField
⟨π⟩ = ℚ(√2·√3)`; C: elementwise `a+b√6` form) are true and the suggested
proof routes correctly line up with what `GaloisGroup.lean`/`FieldTower.lean`
already expose. One deviation from the hints: rather than generalizing
`FieldTower.sqrt2_field_eq` from `d=2` to an arbitrary non-square `d` (as the
hint suggested, for reuse), built the `{1, sqrt6K}`-basis representation
lemma directly and only for `sqrt6K` — same technique, smaller/lower-risk
diff since part C never needed the general case.

## What Was Built

All eight `sorry`s replaced with proofs, in this dependency order:

1. **`sqrt2_mul_sqrt3`** — `Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6`, via
   `Real.sqrt_mul`.
2. **`sqrt6K_coe`** (new, not in the original draft) — `(sqrt6K:ℝ) = √2*√3`
   by `rfl`, tagged `@[simp]`. Added because most later proofs need to
   unfold `sqrt6K`'s real value under `simp`/`push_cast`, and it's a `def`
   so nothing does that automatically without this.
3. **`sqrt6K_pos`**, **`sqrt6K_ne_neg`** — positivity of `√2·√3` as a real
   number, then `x = -x ∧ 0 < x → False` by `linarith`.
4. **`sqrt6K_eq_mul`** — `sqrt6K = ⟨√2⟩ * ⟨√3⟩` in `K`, by `rfl` (subfield
   multiplication is definitionally value-wise multiplication).
5. **`sqrt6K_mul_self`** (new helper) — `sqrt6K * sqrt6K = (6:K)`, proved at
   the `K`-level via `Subtype.ext` + `show` down to the real-number
   computation `(√2·√3)·(√2·√3) = (√2·√2)·(√3·√3) = 2·3 = 6`.
6. **`phantom_middle_fixes_sqrt6K`**, **`sigma_negates_sqrt6K`**,
   **`tau_negates_sqrt6K`** — exactly the hinted route: rewrite `sqrt6K` as
   the product, push each automorphism through `map_mul`, substitute the
   known action on each generator (`phantom_middle_sqrt2/3`,
   `sigma_flips_sqrt2`/`sigma_fixes_sqrt3`, `tau_fixes_sqrt2`/
   `tau_flips_sqrt3`), close with `ring`.
7. **`stabilizer_sqrt6K`** — case split over `four_elts_eq_univ`'s four
   elements; `σ`/`τ` ruled out via `sqrt6K_ne_neg`.
8. **`mem_fixedField_zpowers_phantom_iff`** (new helper, the actual crux of
   D) — `x ∈ fixedField (zpowers π) ↔ π x = x`. `IntermediateField.
   mem_fixedField_iff` only reduces membership to "fixed by every element of
   the subgroup," not just the generator, so this bridges the gap: package
   "`π` fixes `x`" as `π ∈ MulAction.stabilizer (K≃ₐ[ℚ]K) x` (a genuine
   subgroup), then `Subgroup.zpowers_le.mpr` gives `zpowers π ≤ stabilizer x`
   for free, which unpacks to exactly what `mem_fixedField_iff` needs.
9. **`orderOf_phantom_middle`**, **`card_zpowers_phantom_middle`** — `π` has
   order 2 (`orderOf_eq_prime` from `phantom_sq`/`one_ne_phantom`, needing a
   local `Fact (Nat.Prime 2)` instance), hence `Nat.card (zpowers π) = 2` via
   `Fintype.card_zpowers`.
10. **`sqrt6K_isIntegral`**, **`sqrt6K_minpoly`**, **`sqrt6K_finrank`** — the
    same three-step pattern `FieldTower.lean` §1 uses for `Real.sqrt d`
    (`IsIntegral` via the monic witness `X²-6`, minimal-polynomial
    identification via **`triadic_ground_irreducible`** reused directly from
    `GroundAxiom.lean` — that lemma is a pure `ℚ[X]` statement, agnostic to
    which field the root lives in, so it applies to `sqrt6K : K` exactly as
    it does to `Real.sqrt d : ℝ`), giving `[ℚ⟮sqrt6K⟯:ℚ] = 2`.
11. **`fixedField_phantom_middle`** (D) — `ℚ⟮sqrt6K⟯ ≤ fixedField(zpowers π)`
    from step 8 + `adjoin_simple_le_iff`; the reverse degree count from
    `IntermediateField.finrank_fixedField_eq_card` (`[K:fixedField H] =
    Nat.card H`) combined with the tower law and `sqrt2_sqrt3_finrank = 4`
    pins `[ℚ:fixedField(zpowers π)] = 2`, matching step 10's `[ℚ:ℚ⟮sqrt6K⟯] =
    2`; `IntermediateField.eq_of_le_of_finrank_eq` closes it.
12. **`sqrt6K_basis_indep`**, **`sqrt6K_basis`**, **`sqrt6K_field_eq`** (C's
    machinery) — the `{1, sqrt6K}`-basis argument, mirroring
    `FieldTower.sqrt2_basis_indep`/`sqrt2_basis`/`sqrt2_field_eq` exactly but
    instantiated at `sqrt6K` (reusing `sqrt_ne_ratCast 6 six_not_square`,
    both already in `FieldTower.lean`, for the irrationality step) instead
    of generalizing the whole pattern to an arbitrary non-square `d` as the
    hints suggested.
13. **`phantom_middle_fixed_iff`** (C) — chains 8 → 11 → 12: `π x = x ↔ x ∈
    fixedField(zpowers π) ↔ x ∈ ℚ⟮sqrt6K⟯ ↔ ∃a,c, x = a + c·sqrt6K` (basis
    representation), then coerces to `ℝ` and rewrites `sqrt6K` back to
    `√2·√3` via `sqrt6K_coe`.

`Theta0Photon.lean` got one new line: `import Theta0Photon.Algebra.
PhantomFixedField`.

## Problems Encountered and How They Were Fixed

First `lake build` attempt (after writing the full file from the mathlib-API
research pass) surfaced 8 real errors, fixed in one further pass:

- **Redundant `rw [sqrt6K_eq_mul]`** in `sigma_negates_sqrt6K`/
  `tau_negates_sqrt6K`: the very first `rw [sqrt6K_eq_mul, map_mul]` at the
  top of each proof already rewrites *every* occurrence of `sqrt6K` in the
  goal — including the one hidden inside `-sqrt6K` on the RHS — so a second
  `rw [..., sqrt6K_eq_mul]` later in the same proof found nothing left to
  rewrite. Fixed by dropping the redundant occurrence.
- **`aeval` vs `eval₂` lemma mismatch**: `IsIntegral`'s raw existential
  witness goal displays as `eval₂ (algebraMap ℚ K) sqrt6K p = 0`, so
  `eval₂_sub/eval₂_pow/eval₂_X/eval₂_C` apply there — but `minpoly.
  eq_of_irreducible_of_monic`'s root-witness bullet displays as `(aeval
  sqrt6K) p = 0` instead, needing `map_sub/map_pow/aeval_X/aeval_C` (an
  `AlgHom`'s generic ring-hom lemmas, not the `eval₂`-specific ones) even
  though `aeval` is *defined* via `eval₂` — `rw` matches syntactically, not
  up to that unfolding. Diagnosed directly from the `rewrite` tactic's "did
  not find pattern" error showing the actual head symbol (`aeval` not
  `eval₂`) in the goal, not guessed.
- **`apply_fun ... using Subtype.coe_injective` overcomplication**: the
  first draft of `sqrt6K_isIntegral`/`sqrt6K_minpoly` tried to transport the
  polynomial-evaluation goal from `K` to `ℝ` before simplifying, mirroring
  `sigma_hom`'s aroots-membership proof style. Unnecessary and error-prone
  here (the `show` after `apply_fun` didn't match the actual post-simp
  shape) — replaced with a `K`-internal `sqrt6K_mul_self : sqrt6K*sqrt6K =
  (6:K)` helper (itself proved once, at the `ℝ` level via `Subtype.ext` +
  `show`), then both integrality proofs close in one `rw` chain ending
  `sq, sqrt6K_mul_self, sub_self` — no cross-field transport needed at all.
- **`h6 : ((6:K):ℝ) = (6:ℝ)` unsolved by `norm_num`**: `norm_num` alone left
  `↑6 = 6` unsolved for this specific `IntermediateField`-subtype coercion;
  `norm_cast` closed it immediately. `norm_num`'s cast extension apparently
  doesn't reach this coe path the way `norm_cast`'s dedicated simp set does.
- **Ambiguous `algebraMap_mem`**: both a root-level `algebraMap_mem` and
  `IntermediateField.algebraMap_mem` are in scope under `open IntermediateField`
  (root Polynomial import brings the other in). Fixed by qualifying it
  explicitly as `IntermediateField.algebraMap_mem`.
- **Unsolved `↑x = ↑a + ↑b*√6` vs `... = ↑a + ↑b*↑sqrt6K` gap** in the
  backward direction of `phantom_middle_fixed_iff`: an intermediate `have`
  step's proof body ended one line short (`rw [this, hab]` left a residual
  goal equating `sqrt6K`'s two forms) — fixed once `sqrt6K_coe` existed as a
  named `@[simp]` lemma, by folding it into the same `push_cast [sqrt6K_coe]`
  call rather than a bare `rw` with no closing tactic.
- **Second attempt after the above fixes** had exactly 2 residual errors
  (the `h6`/`norm_num` case above, and one more `eval₂`-vs-`aeval` mismatch
  spotted in `sqrt6K_minpoly`'s own root-witness bullet, which had been
  fixed in `sqrt6K_isIntegral` but not yet mirrored there) — fixed the same
  way, and the third build attempt was clean.

## What Was Tested and What Results Mean

```
lake build Theta0Photon.Algebra.PhantomFixedField   # clean, 0 errors
lake build Theta0Photon                             # clean, full library
```

Every one of the 8 target theorems was individually checked via `#print
axioms` (already embedded at the bottom of the file, as the draft's Rule 5
required) against this project's own compiled build, not assumed from the
tactic script alone:

| Theorem | Axioms |
|---|---|
| `sqrt2_mul_sqrt3` | `propext, Classical.choice, Quot.sound` |
| `sqrt6K_ne_neg` | `propext, Classical.choice, Quot.sound` |
| `phantom_middle_fixes_sqrt6K` | `propext, Classical.choice, Quot.sound` |
| `sigma_negates_sqrt6K` | `propext, Classical.choice, Quot.sound` |
| `tau_negates_sqrt6K` | `propext, Classical.choice, Quot.sound` |
| `stabilizer_sqrt6K` | `propext, Classical.choice, Quot.sound` |
| `fixedField_phantom_middle` | `propext, Classical.choice, Quot.sound` |
| `phantom_middle_fixed_iff` | `propext, Classical.choice, Quot.sound` |

No `sorryAx`, no project-defined axioms, no `native_decide`. The one
pre-existing warning in the full-library build (`NavierStokesBridge.
validLevel_fintype` semireducibility) is unrelated and predates this session.

## Final State

- `Theta0Photon/Theta0Photon/Algebra/PhantomFixedField.lean` — all 8 target
  theorems proved, plus 12 supporting lemmas/defs, 0 `sorry`.
- `Theta0Photon/Theta0Photon.lean` — one new import line.
- Not committed to git (per session policy: commit only when the user asks).
  `git status` at end of session shows both files as pending changes
  (`Theta0Photon.lean` modified, `PhantomFixedField.lean` new/untracked).
- No statement's mathematical content was changed from the drafted target;
  no new `axiom`, `sorry`, `native_decide`, `unsafe`, or `implemented_by`
  was introduced anywhere in the diff.
