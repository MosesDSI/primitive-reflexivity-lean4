# Build Summary — Finite Sub-Harmonic Cutoff and the Composite Gradient Bound at `N_max`

**Date:** 2026-09-12
**Project dir:** `PrimitiveReflexivity\` (repo `MosesDSI/primitive-reflexivity-lean4`), specifically `Theta__0_Photon\`
**File touched:** `Theta0Photon/NavierStokes/ContinuumBridge.lean` (extension only — the three theorems from 2026-09-11 were left untouched)
**Objective:** Add a machine-checked finiteness result for geometric refinement levels bounded by a resolution floor, then formally bridge it to the file's existing discrete-lattice gradient bound (`discrete_lattice_prevents_gradient_blowup`) so the two are connected by an actual proof term, not just adjacent prose.
**Outcome:** Nine new declarations added — `ValidLevel`, `validLevel_finite`, `validLevel_fintype`, `h_seq`, `validLevel_iff_h_seq_le`, `IsMaxValidLevel`, `exists_isMaxValidLevel`, `gradient_bound_at_max_valid_level`, `gradient_bound_le_of_max_valid_level` — plus a module-docstring section documenting the two-scale distinction. `lake build Theta0Photon` and `lake build Main` both clean (2627/2627), `#print axioms` on every new declaration shows only `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`. Committed locally as `a81df0e` (on top of `66bf5f8` from 2026-09-11) — not yet pushed; see the note at the end, this is a genuinely open question, not an oversight.

---

## What the coding work actually consisted of

### Part 1 — proving the level count is finite, not just plausible

`ValidLevel L₀ h_min N := h_min ≤ L₀ * (1/√2)^N` says a geometric refinement level `N` is still no finer than a resolution floor `h_min`. The claim "only finitely many `N` satisfy this" sounds obvious from a decay-rate intuition, but turning that intuition into a closed proof means actually producing a concrete bound, not asserting convergence informally. The route: `exists_pow_lt_of_lt_one` (Archimedean field lemma) hands back an explicit witness `N₀` with `(1/√2)^N₀ < h_min/L₀`; `pow_le_pow_of_le_one` (monotone decay of a base in `[0,1]`) then shows every `N ≥ N₀` inherits that same bound; so the valid-level set sits inside `{0, …, N₀ - 1}`, which `Set.finite_lt_nat` already knows is finite. `validLevel_fintype` (a `Fintype` on the corresponding subtype) falls out as a one-line corollary via `Set.Finite.to_subtype` + `Fintype.ofFinite`.

### Part 2 — actually connecting it to the gradient-blowup bound, not just writing about it

The harder and more interesting request was to make `validLevel_finite` *bear on* `discrete_lattice_prevents_gradient_blowup` formally, rather than in a monograph paragraph. The two theorems don't share a variable as originally written — `discrete_lattice_prevents_gradient_blowup`'s `h_min` is a fixed abstract lattice's minimum spacing; `validLevel_finite`'s `h_min` is a floor a *shrinking sequence* is checked against. Before writing anything I said so directly rather than papering over it with prose that would have overclaimed a formal link that didn't exist yet — that's what led to actually building the bridge object:

- `h_seq L₀ N := L₀ * (1/√2)^N` — the spacing at level `N`, made a first-class term instead of leaving it buried inside `ValidLevel`'s definition, with `validLevel_iff_h_seq_le` (`Iff.rfl` — the two are definitionally the same fact stated two ways) connecting them cheaply.
- `IsMaxValidLevel` — not just "a valid level exists" but "the *greatest* valid level," because the interesting quantity for a gradient bound is the *finest* grid that hasn't yet dropped below the floor — the worst-case-but-still-safe spacing.
- `exists_isMaxValidLevel` — constructs that maximum as an actual term, `hfin.toFinset.max' ⟨0, h0mem⟩`, off the finite set `validLevel_finite` already proved exists, under the one honest extra hypothesis needed to make "the maximum" well-defined at all: `h_min ≤ L₀` (level `0` itself must be valid, or there's no maximum to speak of — an explicit, not hidden, precondition).
- `gradient_bound_at_max_valid_level` instantiates `discrete_lattice_prevents_gradient_blowup` at that computed spacing; `gradient_bound_le_of_max_valid_level` is the actual bridge inequality, showing that bound is in particular no worse than the fixed-floor bound `2√E_total / h_min`, because `h_min ≤ h_seq L₀ N_max` by construction.

The design choice worth flagging: `NodeSpace` stayed fully abstract in both new theorems, exactly matching how `discrete_lattice_prevents_gradient_blowup` was already written. I did not invent a concrete lattice type (e.g. a scaled-`ℤ` model) to "instantiate" the bridge — the composition works entirely through the derived scalar `h_seq L₀ N_max`, which preserves the generality of the original theorem instead of narrowing it to one geometric model. That was a judgment call I flagged explicitly rather than assumed, and it was confirmed as the right one before proceeding.

---

## Three real bugs, all caught by compiling, none by re-reading the proof sketch

1. **`push_neg` "made no progress."** After `by_contra hlt` on a goal of the form `N < N₀`, the standard next step is `push_neg at hlt` to turn `¬ (N < N₀)` into `N₀ ≤ N`. In this Lean/Mathlib pin, `by_contra` had already normalized the hypothesis into the `≤` form itself, so `push_neg` had nothing left to do and errored rather than silently no-opping. Fixed by dropping the redundant tactic and going straight to `not_lt.mp hlt`. Small, but a good reminder that "the standard idiom" isn't guaranteed idempotent-safe across tactic/version changes — the compiler is the only reliable source of truth for what a given proof state actually looks like.

2. **An `instance` that can't be an instance.** My first pass at `validLevel_fintype` declared it as `noncomputable instance`, matching the task's phrasing ("provide the `Fintype` instance"). Lean rejected it outright: *"This instance has 2 arguments that cannot be inferred using typeclass synthesis"* — `hL : 0 < L₀` and `h_min_pos : 0 < h_min` are ordinary propositional hypotheses, not instance-resolvable classes, so an `instance` with them as explicit non-instance arguments is simply malformed, not just discouraged. The fix is a `noncomputable def` instead — same corollary, callable exactly the same way, just not auto-triggered by typeclass search (which was never going to happen anyway, since nothing in scope could conjure `hL`/`h_min_pos` out of nowhere). The same fix pattern applies to the next bug.

3. **`h_seq` needed `noncomputable`, `ValidLevel` didn't.** `ValidLevel` returns a `Prop` and compiled fine as a plain `def` despite using `Real.sqrt` internally — propositions erase at compile time, so noncomputability inside one is invisible to the compiler. `h_seq` returns an actual `ℝ`, and failed with *"depends on `Real.instDivInvMonoid`, which is `noncomputable`"* the moment it was declared as a plain `def`. Same underlying real-number arithmetic in both places; only the one that has to produce an actual runtime value needs the marker. Easy to get backwards if you pattern-match on "I already have a `Real.sqrt`-using `def` two declarations up that compiled fine."

---

## The Mathlib-lemma discipline that made this fast instead of a guessing exercise

Rather than recall lemma names from training and hope they still exist in this project's pinned rev (`v4.33.1`, commit `0df444a`), every non-trivial lemma used here was found by grepping the actual local Mathlib source checked out under `.lake/packages/mathlib`, which this project already has cached:

- `exists_pow_lt_of_lt_one` — `Mathlib/Algebra/Order/Archimedean/Basic.lean`.
- `pow_le_pow_of_le_one` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean` (deliberately *not* `pow_le_pow_right_of_le_one'`, the ordered-monoid multiplicative sibling one file over in `Order/Monoid/Unbundled/Pow.lean` — same-sounding name, different hypothesis shape, doesn't fire cleanly here since `MulLeftMono ℝ` doesn't hold in general).
- `lt_div_iff₀` — the `₀`-suffixed `GroupWithZero`-era name (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean`), not the pre-refactor `lt_div_iff`.
- `Set.finite_lt_nat`, `Set.Finite.toFinset` / `.mem_toFinset`, `Finset.max'` / `.max'_mem` / `.le_max'` — chained together to get an actual computed `N_max`, not just an existence claim.

This is the same discipline as the 2026-09-11 session (grep the pinned source, don't guess), and it's the reason zero lemma-name errors showed up on the *second* build attempt for the harder composite theorem — only the three genuine logic/declaration bugs above did.

---

## Verification

- `lake build Theta0Photon` — 2627/2627, clean, both before and after the module-docstring update.
- `lake build Main` — 2627/2627, clean (confirms no transitive breakage against the executable target).
- `#print axioms` run against the installed module (not a scratch file) for every new declaration — `validLevel_finite`, `validLevel_iff_h_seq_le`, `exists_isMaxValidLevel`, `gradient_bound_at_max_valid_level`, `gradient_bound_le_of_max_valid_level` — all `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
- Scratch axiom-check files lived outside the repo (Windows temp), deleted after each use; confirmed absent from `git status` both times.

## Docstring addition

The module docstring now has a dedicated section distinguishing the two scales that must not be conflated: `h_seq L₀ N_max` (the **dynamic sub-harmonic lattice spacing** — derived from the refinement process, shrinks with every level) versus `h_min` (the **extrinsic material yield floor** — an atomic-/Nyquist–Brillouin-type cutoff, fixed and external to the refinement process), with `gradient_bound_le_of_max_valid_level` named as the bridge inequality between them.

## Git

Committed locally: `a81df0e` on `master`, on top of `66bf5f8` (2026-09-11's `ContinuumBridge.lean` addition). Staged only `Theta0Photon/NavierStokes/ContinuumBridge.lean` both times; `git status` confirmed clean of the surrounding untracked/deleted files that predate this work.

**Open item, not resolved by default:** `origin/master` is still at `a7ea108`, two commits behind local `master`. The standing practice is that engineering-report summaries get pushed without re-asking each time — but pushing this report's commit would, as an unavoidable consequence of linear git history, also push `66bf5f8` and `a81df0e`, and `66bf5f8`'s own build summary explicitly recorded "local commit only, per explicit instruction — nothing pushed." That instruction and the "always push engineering reports" default now point in different directions, so which one governs here is being confirmed with Jonathon directly rather than assumed either way.
