# SimulationExchange: Placement, Reproduction, Mathlib Bridge, and CI Integration

**Date:** 2026-10-10
**Project:** `PrimitiveReflexivity` (root repo, `SimulationExchange/` standalone
bare-Lean package, `Theta__0_Photon/Theta0Photon` one new Mathlib file, CI)
**Toolchain:** `leanprover/lean4:v4.33.1` throughout; `SimulationExchange/` is
Mathlib-free, `Theta__0_Photon` pinned to the same Mathlib revision as the
rest of the repo.

## Objective

Jonathon handed off a standalone bare-Lean Lake package (`SimulationExchange/`)
built by Claude on claude.ai ("outside"), delivered as a folder plus its own
build summary in `Downloads/`, deliberately kept outside the repo to avoid
confusion. Its own build summary's §6 set four tasks for Claude Code
("inside"): (1) place it in the repo and independently reproduce its audit
before trusting it; (2) wire it into CI; (3) build the Mathlib bridge
instantiating its two theorems at `R = ℝ`; (4) sync the repo's documentation.
Task 4's one `.docx` sub-item (an etymology essay draft not present in this
repo) was explicitly deferred by Jonathon; everything else was completed this
session.

## What Was Reviewed First

Read all five `SimulationExchange/SimulationExchange/*.lean` files and
`AxiomCheck.lean` end-to-end against the handoff build summary's own claim
tables (Core.lean's Theorem A/`faithful` and Theorem B/`no_direct_rule`,
Model.lean's kernel-checked instructure ring `Inst d₁ d₂`, Instances.lean's
trap non-vacuity and ring-level necessity counterexamples, Walkers.lean's
coincidence-only-at-origin and dominance-never-ties, Boundary.lean's exact-
integer 0.5-boundary results) — every declaration matched what the tables
described, no discrepancies found. Computed SHA-256 of all six delivered
`.lean` files; all six matched the handoff document's checksums exactly, so
nothing was altered in the Downloads→session transfer.

## What Was Built

### Phase 1 — Place and reproduce (commit `f34f74a`)

Copied `SimulationExchange/` into the repo root as its own standalone Lake
package (own `lakefile.toml`, `lean-toolchain`, no Mathlib — same spirit as
`R3_bare_lean/`, but a real `lake`-built package rather than a `lean
<file>.lean`-checked one). Added `SimulationExchange/.lake` to `.gitignore`
(the existing `/.lake` line was root-anchored only). Independently reproduced
every claim in the handoff's §5 audit, from scratch, before committing:

```
lake build                                             # 8 jobs, clean, no warnings
grep sorry|native_decide|axiom|admit|implemented_by|@[extern]   # no matches
lake env lean AxiomCheck.lean                          # all 53 declarations within
                                                         # [propext, Classical.choice, Quot.sound]
lake env leanchecker --fresh SimulationExchange.Instances   # exit 0
lake env leanchecker --fresh SimulationExchange.Walkers     # exit 0
lake env leanchecker --fresh SimulationExchange.Boundary    # exit 0
```

Also updated `Simulation_Formal_Definition.md` (S2 row), `ROADMAP_LEDGER.md`
(new Tier 1 row), and `Instructure_Formal_Definition.md` (new N5/E1 rows) to
cite the new bare-Lean results without overclaiming what they don't cover
(the `R = ℝ` instantiation, the asymptotic ½ in-step frequency).

### Phase 2 — CI (commit `f34f74a`, same commit as Phase 1)

Added a `simulation-exchange` job to the root `.github/workflows/
lean_action_ci.yml`, using `leanprover/lean-action@v1`'s native
`lake-package-directory`, `leanchecker`, and `axiom-audit` inputs (its
default allowlist, `propext,Classical.choice,Quot.sound`, already matches
the trust footprint verified in Phase 1 — no customization needed).

### Phase 3 — Mathlib bridge (commit `ff43e33`)

Added `SimulationExchange` as a local path-dependency of `Theta__0_Photon`
(`[[require]] name = "SimulationExchange", path = "../SimulationExchange"`
in its `lakefile.toml`; `lake update SimulationExchange` to register it in
the manifest — confirmed this only resolved the local path, no network
fetch, since Mathlib's own cache was already fully decompressed).

Before writing any Lean, confirmed interactively (the build summary's own
explicit instruction: report back if missing, don't work around it) that
Mathlib's `ℝ` resolves both instances `SimulationExchange.faithful` and
`.no_direct_rule` need: `#check (inferInstance : Lean.Grind.CommRing ℝ)` and
the `Lean.Grind.IsCharP ℝ 0` analogue both elaborate with no extra instance
work. (The unqualified names `CommRing`/`IsCharP` are ambiguous between
Mathlib's own classes and `Lean.Grind`'s — fully qualifying resolved it; the
ambiguity itself is not a problem since application sites never write the
class name, only call the already-elaborated bare-Lean theorems.)

Wrote `Theta__0_Photon/Theta0Photon/Algebra/SimulationExchangeBridge.lean`:

- `nonSquare_iff_not_isSquare` — bridges `SimulationExchange.NonSquare`
  (`∀r, r·r≠d`) to Mathlib's `¬IsSquare`, in the same spirit as
  `GeneralFieldTower.lean`'s existing one-directional bridge lemmas but as a
  single `iff` (pure logic, no extra hypothesis needed either direction).
- `faithful_real`, `no_direct_rule_real` — Theorem A and B instantiated at
  `R = ℝ`, `s = Real.sqrt d₁`, `t = Real.sqrt d₂`.
- `fract_faithful`, `fract_no_direct_rule` — the same two theorems restated
  directly in terms of `Int.fract`, matching
  `Simulation_Formal_Definition.md`'s S2 row literally (`Int.fract (n*√d) =
  Int.fract (m*√d) → n = m`, and the "no rational-affine rule between
  fractional phases" form for Theorem B, for arbitrary `p q : ℚ` cleared to
  integers via `p.num, p.den, q.num, q.den`).
- `sqrt_notMem_agrees_with_no_direct_rule` — the handoff's requested
  cross-check "`no_direct_rule` instantiated at ℝ agrees with
  [`GeneralFieldTower.sqrt_notMem`]," built as: assume the negation of
  `sqrt_notMem`'s conclusion (`√d₂ ∈ ℚ⟮√d₁⟯`), extract rationals `a, c` via
  `GeneralFieldTower.sqrt_field_eq` (which does need `hd1`, unlike
  `no_direct_rule` itself), clear denominators into integers `v = a.den·c.den
  ≥ 1`, `u = c.num·a.den`, `w = a.num·c.den`, and feed them to
  `no_direct_rule_real` at tick `n=1`, offsets `k₁=k₂=0` — producing `False`,
  i.e. confirming the two independently-proved facts cannot both be false at
  once. This never calls `sqrt_notMem` itself and never re-derives its
  field-theoretic proof, per the handoff's explicit instruction not to
  re-prove it.

## Problems Encountered and How They Were Fixed

- **A long, initially-misdiagnosed environment failure.** Building anything
  that imports `Theta0Photon.Algebra.GeneralFieldTower` (which pulls in a
  large fraction of Mathlib — field theory, linear algebra, analysis, ~2370
  transitive modules) failed reproducibly with `failed to read file
  ...olean` / `...olean.private`, a different random file each time, 8
  consecutive attempts across both the Bash and PowerShell tools. Ruled out,
  in order: a stale/corrupt cache (`lake exe cache get` reported everything
  already present); the new `SimulationExchange` import itself (isolated —
  importing it alone, with nothing else, built cleanly in 2 seconds); an
  MSYS2 `ulimit -n` file-descriptor cap (reproduced identically from native
  PowerShell, so not a Bash-shell artifact); and a leaked/zombied prior
  `lean.exe`/`lake.exe` process (none found). Jonathon correctly diagnosed it
  as Windows Defender real-time scanning colliding with a burst-open of
  ~2370 freshly-built `.olean` files in one process (the exact same import
  set had built cleanly minutes earlier, during the slower, one-file-per-
  process full-library build, which gives Defender's scanner time to keep
  up) — his suggested remediation (process cleanup check, then a cache
  refresh via `lake exe cache get`) was what actually cleared it; the next
  attempt succeeded in 57s and all subsequent builds were reliable. 14
  VS Code processes were also running with large handle counts (one with
  1320), a plausible contributing/alternative lock source, but were
  deliberately left untouched rather than killed, since that could have
  discarded Jonathon's unsaved editor state — the fix came from the less
  invasive steps instead.
- **`fract_no_direct_rule`, a real proof bug (not environmental).** An
  over-eager `simp only [Int.fract] at h` unfolded the hypothesis before a
  later `rw [h]` needed to match its un-unfolded `Int.fract (...)` form
  against the goal — `rw` failed to find the pattern. Fixed by deleting the
  premature `simp`; `Int.fract` never needed to be unfolded at all, since
  the final arithmetic step treats it as an opaque real atom throughout.
- **Same lemma, a second small bug once the first was fixed:** the trailing
  `ring` after `field_simp` errored with "no goals to be solved" — `field_simp`
  had already closed the goal outright. Deleted the redundant `ring`.
- Both bugs were caught by the compiler, not missed — `#print axioms` on
  every new declaration was checked regardless (per the standing habit
  logged in the previous session's build summary: a clean build is
  necessary but not sufficient).

### Phase 4 — CI follow-up: dead nested workflow (commit `45e9ee8`)

While wiring CI in Phase 2, noticed `Theta__0_Photon/.github/workflows/
lean_action_ci.yml` already existed but was inert: GitHub Actions only reads
workflow files from the *repository root's* `.github/workflows/`, never a
nested copy, so it had never actually run. Flagged this to Jonathon rather
than silently fixing it; he asked for it to be wired into the root workflow
properly. Added a `theta-0-photon` job to the root `lean_action_ci.yml` (same
`lake-package-directory`/`leanchecker`/`axiom-audit` pattern as the
`simulation-exchange` job) and deleted the non-functional nested file.

## What Was Tested

```
lake build                                              # SimulationExchange/ — 8 jobs, clean
lake env lean AxiomCheck.lean                            # 53 declarations, all within
                                                          # [propext, Classical.choice, Quot.sound]
lake env leanchecker --fresh SimulationExchange.{Instances,Walkers,Boundary}  # exit 0, all three
lake build Theta0Photon.Algebra.SimulationExchangeBridge # clean, after the two proof fixes
lake build Theta0Photon                                  # full library, 2633/2633 jobs, clean
lake env leanchecker --fresh Theta0Photon.Algebra.SimulationExchangeBridge    # exit 0
```

Every new declaration in both packages was individually `#print axioms`-
checked, not just built: `[propext, Classical.choice, Quot.sound]` only
(several `SimulationExchange` necessity/instance lemmas use no axioms at
all), zero `sorryAx`, zero new home-rolled axioms, zero `native_decide`.

**Scope limit, stated once:** this session did not touch the asymptotic ½
in-step frequency (needs Weyl equidistribution/Kronecker density — already
tracked as open in `ROADMAP_LEDGER.md`'s "Next Upgrade Targets"), nor the
etymology essay's Propositions 2–4 (walk/fall handedness, the `σ` exchange,
`W·F = m²−n²/2`), nor the `Etymology_Section_5_4.docx` status-table update
the original handoff mentioned — that file isn't present anywhere in this
repo, and Jonathon explicitly deferred it for this session.

## Final State

Three commits this session, all on `master`, in order:

```
f34f74a  feat(bare-lean): add SimulationExchange, the two-incommensurable-walkers build
ff43e33  feat(mathlib): bridge SimulationExchange to R = ℝ in Theta__0_Photon
45e9ee8  ci: wire Theta__0_Photon into the root CI workflow
```

All pushed to `origin/master`. Working tree clean except the same
pre-existing untracked scratch files present at session start (none added,
none removed, none touched — confirmed via `git status` before every stage/
commit). `SimulationExchange/` (8 jobs) and the full `Theta__0_Photon`
library (2633 jobs) both build clean as of the final commit. See the
companion summary filed in `Compiler/Build_Summaries/` for the canonical
cross-project copy of this record.
