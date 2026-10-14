# Meeting Walker and Switching Table: Placement, Reproduction, and Paper Audit

**Date:** 2026-10-13
**Project:** `PrimitiveReflexivity` (`SimulationExchange/` standalone bare-Lean package; two paper drafts converted to Markdown at the repo root)
**Toolchain:** `leanprover/lean4:v4.33.1` (local Windows install via elan), no Mathlib touched

## Objective

Jonathon handed off `Downloads/For Claude Code Review/`, which held two claude.ai ("outside") builds with their own build summaries (2026-10-11 `Meeting.lean`, 2026-10-12 `Switching.lean`), the updated `SimulationExchange.lean` and `AxiomCheck.lean`, a set-aside `Systems.lean`, and two Word drafts (*Two Walkers and a Tick*, *Discrete Evidence in Neuroscience*). The tasks were to review the Lean files, bring them into the repo, verify them in the usual way, and convert the Word drafts to `.md`. The Markdown drafts are **not to be pushed to git yet**.

## What Was Reviewed First

- Read the `.lean` files and both handoff summaries end to end.
- Computed SHA-256 of every delivered file. All four checksums claimed in the handoffs match exactly (`Meeting.lean` 99476d61…, `Switching.lean` 99f54c72…, `SimulationExchange.lean` f1079196…, `AxiomCheck.lean` 5a2fb725…). The combined `SimulationExchange.lean`/`AxiomCheck.lean` are the 2026-10-12 versions, which already contain the 2026-10-11 additions.
- Confirmed with `diff` that the new `AxiomCheck.lean` changes nothing in the repo's existing 55 lines; it only appends 32 lines.

## What Was Built

- `SimulationExchange/SimulationExchange/Meeting.lean` (new, §17–§18): `meeting_faithful` plus three necessity witnesses and three non-vacuity instances.
- `SimulationExchange/SimulationExchange/Switching.lean` (new, §19–§23): 25 declarations covering `switch p q` on `Inst d₁ d₂`, ring-map properties, XOR composition, fixed sets, and `switch_unique` (the table is forced), with a necessity witness for each of its five hypotheses.
- `SimulationExchange/SimulationExchange.lean`: two new imports.
- `SimulationExchange/AxiomCheck.lean`: 32 new `#print axioms` lines (85 total).
- `Two_Walkers_and_a_Tick.md`, `Discrete_Evidence_in_Neuroscience.md` (repo root, **untracked, not to be committed yet**). They were converted with a small python-docx script that keeps the headings, lists, tables, grey boxes (rendered as one-cell tables), Consolas code, bold/italic, and footnotes (as `[^n]`). The documents contain no equations or images, so nothing was lost.
- `Systems.lean` was **not** placed. Both handoffs say it was set aside, and it is not imported anywhere. It was checked standalone in the scratchpad only (see below).

## Problems Encountered and How They Were Fixed

- **Converter over-escaping.** The first conversion escaped `_` inside bold runs. Those runs contain literal backticks around Lean names, so `coincidence_only_at_origin` was rendered as `coincidence\_only\_at\_origin`. I changed the converter to escape only `*` and reran it. A Python count confirmed zero `\_` sequences remain. (Git Bash `grep '\\_'` gave a false positive count here; it is not a reliable check.)
- **Slow recursive grep.** `grep -r` over the repo walked Mathlib's `.lake` trees and timed out. I switched to the ripgrep-based search, which skips `.lake`.
- No Lean proof needed any change. Every delivered file builds exactly as delivered.

## What Was Tested and What Results Mean

```
lake build                                         # 10 jobs, clean (Meeting 45s, Switching 45s)
lake env lean AxiomCheck.lean                      # 85 lines, exit 0; every footprint within
                                                   # [propext, Classical.choice, Quot.sound]
grep sorry|native_decide|axiom|admit|implemented_by|extern   # no matches
lake env leanchecker --fresh SimulationExchange.Meeting      # exit 0
lake env leanchecker --fresh SimulationExchange.Switching    # exit 0
lean Systems.lean   (scratchpad, standalone, not placed)     # exit 0; footprints [propext] / [propext, Quot.sound]
```

The Meeting footprints match the 2026-10-11 table exactly.

### Audit findings (claims against formalization)

1. **Footprint count miscount (handoff 2026-10-12, minor).** The handoff says "16 of [25 Switching declarations] use `propext` alone or `propext, Quot.sound`." The audit gives **18**. Only 7 use `Classical.choice`: `switch_mul`, `pi_fixed_iff`, `sigma_fixed_iff`, `tau_fixed_iff`, `additive_intCast_mul`, `switch_unique`, `switch_satisfies_hypotheses`. The trust claim itself is unaffected.
2. **`switch_unique_needs_x₁` / `_x₂` state less than the handoff says.** Per the handoff, the identity "meets the other hypotheses for σ [τ], is not σ [τ]". The Lean statements only assert the other generator hypothesis plus the inequality. Additivity, `f 1 = 1`, and the product rule for `id` are true but not recorded in the theorem. The other three necessity witnesses do state every remaining hypothesis.
3. **Real-number bridge gap (*Two Walkers*, §2.1, §2.2 Theorem C).** The paper says all theorems hold "through a separate bridge, for the real numbers". It states Theorem C with `√` and `mod 1`. `SimulationExchangeBridge.lean` bridges only `faithful` and `no_direct_rule`. There is no `meeting_faithful_real` yet. The Boundary/Switching results are not bridged either. This is the handoff's optional task 3.
4. **Tier inconsistency on "switch commutes with the dynamics".** *Two Walkers* §4.1 marks it **[VERIFIED]** (`switch_add`/`switch_mul`/`switch_walker`), but the §5.1 grey box still says **[PROVED BY HAND]** for the engine. *Discrete Evidence* §1 also says PROVED BY HAND. Both can now be raised to VERIFIED in the integer model.
5. **Stale status (*Discrete Evidence*, Appendix A).** It says `meeting_faithful` is "pending placement in the repository". It is now placed and verified locally, but not yet committed.
6. **Appendix A hypothesis column (*Two Walkers*, minor).** `switch_unique` is listed with "additive, f 1 = 1, product rule". The theorem also takes the two generator hypotheses `hx₁`, `hx₂`, which footnote 9 counts among its "five hypotheses".

All other cited declarations exist under the names given: `card_Gal_eq_four`, `isKleinFour_K`, `fixedField_phantom_middle`, `stabilizer_sqrt_prod`, `chiral_sign_law`, `sample_decomp_two`, plus every SimulationExchange name. The cited Boundary hypotheses match the Lean signatures (`wall_never_hit` needs only char 0; `fixed_points_never_occupied` needs `NonSquare d` and `1 ≤ n`).

**Scope limit, stated once:** this session verified the kernel-checked statements and the tiers that cite them. It did not assess the neuroscience mappings marked INTERPRETIVE/RESONANCE, and it did not check bibliographic details. *Discrete Evidence* itself flags the references as compiled from memory.

## Follow-up (same day): Commit, Ledger, Theorem C Bridge

Jonathon then asked for all three of the pending items:

- **Theorem C at `R = ℝ`.** Added `meeting_faithful_real` and `fract_meeting_faithful` to `Theta__0_Photon/Theta0Photon/Algebra/SimulationExchangeBridge.lean`. They follow the existing `faithful_real`/`fract_faithful` pattern: `s = √d₁`, `t = √d₂`, and the hypothesis is only `¬ IsSquare (d₁·d₂)`. The fract form is `Int.fract (n(√d₁−√d₂)) = Int.fract (m(√d₁−√d₂)) → n = m`. Both built on the first attempt. Results: `lake build Theta0Photon.Algebra.SimulationExchangeBridge` 2380 jobs clean; full `lake build Theta0Photon` 2633 jobs clean; `leanchecker --fresh` on the bridge exit 0; both new declarations within `[propext, Classical.choice, Quot.sound]`; no `sorry`/`native_decide`/`axiom`. The full build shows one `warn.classDefReducibility` warning. It comes from `NavierStokes/ContinuumBridge.lean`, which existed before this session and was not touched. This closes audit finding 3 for Theorem C. The Boundary and Switching results are still bridged only in the integer model.
- **Ledger.** In `ROADMAP_LEDGER.md`, the SimulationExchange row now covers `Meeting.lean` and `Switching.lean` (85 declarations, five modules leanchecker-clean, the switching table hypothesis-free) and adds "only four automorphisms" as not yet built. The bridge row now covers the two new Theorem C instances.
- **Commits.** Made on `master`, not pushed: bare-Lean files, the Mathlib bridge, and docs (ledger plus this summary). The two converted paper drafts stay untracked.

## Final State

- `SimulationExchange/` (10 jobs) and `Theta__0_Photon` (2633 jobs) both build clean.
- Committed locally on `master`, **not pushed**, pending Jonathon's go-ahead.
- `Two_Walkers_and_a_Tick.md` and `Discrete_Evidence_in_Neuroscience.md` are at the repo root, untracked by request. Audit findings 4–6 (tier labels and appendix wording in the papers) have not been edited into the drafts. With the bridge in place, *Two Walkers* §2.1's "through a separate bridge, for the real numbers" is now true for Theorems A, B and C.
- Remaining optional target: the Galois intertwining cross-check (`switch p q` ↔ `sigma_K`/`tau_K`/`phantom_middle`). The open target is "only four automorphisms" of `Inst d₁ d₂`.
