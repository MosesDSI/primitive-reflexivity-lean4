# LTromino (outside build): Verification, §4.3 WalkerBridge, and Placement

**Date:** 2026-10-15
**Project:** `PrimitiveReflexivity`, new core-only package `LTromino/` (placed at the repo root in Part 2)
**Toolchain:** `leanprover/lean4:v4.33.1` (local Windows install via elan), no Mathlib

## Objective

Jonathon handed off `Downloads/For Claude Code Review/`, which holds a claude.ai ("outside") LTromino build. The task was to verify its proposed theorems in Lean: rebuild, re-audit the axioms, and check that the statements match the claims in its build summary and in the repo documents it cites.

## What Was Reviewed

- The folder holds five files. `LTromino_All_Files.txt` is the **current, complete bundle**: BUILD_SUMMARY (with three later updates), AXIOM_AUDIT.txt, lakefile, toolchain, `LTromino.lean`, and `Base`, `Tiling`, `Equivariance`, `DiagonalBridge` and `AxiomCheck`.
- The loose `Base.lean`, `Tiling.lean`, `BUILD_SUMMARY.md` and `AxiomCheck (1).lean` are an **earlier snapshot**.
  - Loose `Base.lean` matches the bundle except for a trailing newline.
  - Loose `Tiling.lean` is a pre-repair draft.
  - Loose `BUILD_SUMMARY.md` and `AxiomCheck (1).lean` are the 69-declaration version.
- I extracted the bundle into a scratch lake project and read all four modules in full.

## What Was Built

Nothing was placed in the repo. Two scratch projects were built under the session scratchpad:
- `ltromino/` holds the bundle.
- `loose/` holds the loose `Base.lean` and `Tiling.lean`.

## Problems Encountered and How They Were Fixed

- **Slow recursive grep.** As on 2026-10-13, `grep -r` walked the `.lake` trees and timed out. I switched to the ripgrep search scoped to the `PrimitiveReflexivity/` and `Theta__0_Photon/` source trees.
- **Self-caught mistake: wrong toolchain.** I ran `lean core_check.lean` from the scratchpad root, which has no `lean-toolchain`. elan's default then started downloading Lean 4.35.0. I stopped the task and reran via `lake env lean` inside the 4.33.1 project.
- No proof in the bundle needed any change.

## What Was Tested and What Results Mean

Commands and results:

```
lake build                                  # 7 jobs, clean, 0 warnings (Base 40s, Equivariance 32s)
lake env lean LTromino/AxiomCheck.lean      # 153 lines, exit 0
diff vs bundled AXIOM_AUDIT.txt             # identical (after stripping the LTromino. prefix)
declared theorems vs audited names          # 153 = 153, none missing
grep sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque   # no matches
lake env leanchecker --fresh LTromino.{Base,Tiling,Equivariance,DiagonalBridge}   # all exit 0
```

**Axiom totals.**
- 140 of 153 theorems depend on no axioms. That includes all of `Base`, `Tiling` (`tile_correct`, `touches_middle_iff`, the area chain and the necessity results) and `DiagonalBridge`.
- The other 13 are all in `Equivariance.lean` and carry `[propext, (Classical.choice,) Quot.sound]` via `simp`/`omega`/`List.perm_iff_count`.

**Core-lemma finding, confirmed.**
- These core lemmas depend on `[propext]` in 4.33.1: `Nat.mul_assoc`, `List.length_append`, `List.length_map`, `Nat.sub_add_cancel`, `Nat.add_sub_cancel`, `Nat.beq_refl`, `Bool.and_eq_true` and `Nat.add_left_cancel`.
- These are axiom-free, as the bundle says: `Nat.le_of_ble_eq_true`, `Nat.eq_of_beq_eq_true`, `Nat.le.dest`, `Nat.lt_or_ge`, `Nat.add_add_add_comm`, `Nat.pow_succ` and `Prod.mk.inj`.

**Loose `Tiling.lean` does not compile.** It has 13 errors: unsolved goals at 180 and 188, "no goals" at 444, and type mismatches from 477 onward. The bundle's diff fixes exactly these lines, so the loose file is superseded and should not be used.

**Statement-level checks.**
- `TilesS` is the full specification:
  - for all `cx cy : Nat`, coverage equals 1 exactly on an on-board cell that is not the hole, and 0 everywhere else, off-board cells included;
  - `covers` is a 2×2 block minus one corner, so every tile is an L.
- `tile_correct` requires `hx hy < 2^n`. It matches its claim.
- The D₄ and V₄ facts in `Base` are decided over every bit. Their statements match the descriptions: the centre is {id, π}, `chiralBits` is onto with kernel {id, π}, and the stabilizer of each L is {id, its own diagonal reflection}.
- `tile_equivariant` is `List.Perm`, which is the correct strength. `equivariance_not_list_equality` shows that list equality fails.
- `vD1 = (1,1)` and `vD2 = (1,−1)` match `CenteredKernel.D1` and `D2`, with index 0 ↦ 1 (`CenteredKernel.lean:58,61`).
- `chiral_swap_on_cells` has the same shape as `Boundary.lean` §15b's `D₁ a₂ a₁ = D₁ a₁ a₂ ∧ D₂ a₂ a₁ = −D₂ a₁ a₂`.

**Scope points (claims broader than the Lean statement):**
1. **The Two Walkers §4.3 upgrade.**
   - The summary says `det_eq_sign` upgrades §4.3 from PROVED BY HAND to VERIFIED.
   - §4.3 is about flipping walkers on the *torus of phases*. `det_eq_sign` is about the eight symmetries of the 2×2 cell model.
   - The identification "walker flip = `mirrorX`/`mirrorY`" is not formalized.
   - The tag should name the 2×2 model, or keep PROVED BY HAND with a pointer to `det_eq_sign`.
2. **The `DiagonalBridge` link to `CenteredKernel`.**
   - `DiagonalBridge` does not import `CenteredKernel`; it is core-only and has no ℝ. So "the two splits agree" rests on integer copies whose definitions mirror the originals, not on a kernel-checked link.
   - `decomp_no_halving` is `sample_decomp_two`×2 only for the four 0/1 samples, not for every sample.
   - These are accurate as a discrete counterpart, but they should not be cited as a verification *of* `CenteredKernel`.
3. **"No hypothesis on the hole."**
   - `tile_equivariant` does hold for every `hx hy`.
   - Off the board, though, `actB` is a truncated subtraction, not a symmetry, and `tile` is not a tiling. `equivariant_off_board_hole` is a statement about how truncation clamps the hole, not about geometry.
   - The meaningful content is for on-board holes.
4. **Necessity results are single instances.**
   - `tiling_needs_hole_on_board` covers n = 0 with the hole at (1,0).
   - `tiling_needs_single_hole` covers the 2×2 with the D1 pair removed.
   - Both are stated that way in Lean. They are witnesses, not general impossibility theorems.
5. **`equivariant_8x8_pi` is weaker than `Perm`.** It checks containment in both directions, which is set equality, not multiplicity. The general multiset statement is `tile_equivariant` itself.

## Final State

- The bundle in `LTromino_All_Files.txt` is verified as delivered:
  - it builds cleanly on 4.33.1;
  - the kernel replay passes;
  - the axiom audit is reproduced exactly (153 theorems, 140 axiom-free);
  - there is no `sorry` and no custom axiom.
- The loose `.lean` and `BUILD_SUMMARY.md` files are a stale earlier snapshot, and the loose `Tiling.lean` does not compile.
- Not done yet, pending Jonathon's go-ahead:
  - placing `LTromino/` in the repo, beside `SimulationExchange/`;
  - adding a CI target;
  - adjusting the §4.3 tag in *Two Walkers and a Tick*.

---

# Part 2: §4.3 WalkerBridge and placement in the repo

## Objective

Jonathon asked that §4.3 of *Two Walkers and a Tick* be made fully verified in Lean rather than left as a hand proof or demoted. The steps:
- a `WalkerBridge.lean` with `d4_to_walker`, `walker_matrix_det_eq_d4_det` and `universal_walker_flip_eq_sign`;
- wiring it into the bundle and the lakefile;
- updating §4.3 to VERIFIED;
- `lake build` plus `leanchecker`, then committing `LTromino/` beside `SimulationExchange/`.

## Design Correction Made Before Building

As specified, `d4_to_walker` would have been a relabelling of `Base.mat`, and the two theorems would hold by `rfl` / `det_eq_sign` without mentioning walkers. That would have repeated the very mismatch found in Part 1: the paper claims more than the Lean states.

So the walker matrix is **computed from the repo's walker operations**:
- `Inst.switch g.a g.b` (the §4.1 world table in `SimulationExchange/Switching.lean`);
- preceded, when `g.s` is set, by `exchange` (the walkers trade generators, §15b);
- each applied to the unit generators x₁ and x₂.

The requested names and signatures are kept. The non-circular content is in the representation theorems:
- `switch_represents` and `exchange_switch_represents` show the matrix is what the operation does to the walker coordinates (b, c) of every element of every `Inst d₁ d₂`.
- `walker_matrix_eq_mat` then identifies it with D₄'s matrix.

## What Was Built

- `LTromino/` at the repo root:
  - `lakefile.toml` requires `SimulationExchange` with `path = "../SimulationExchange"`;
  - `lean-toolchain` is 4.33.1;
  - the modules are `Base`, `Tiling`, `Equivariance` and `DiagonalBridge` (as delivered, unchanged) and **`WalkerBridge`** (new, 17 theorems);
  - `AxiomCheck.lean` gains 17 lines (170 total);
  - the generated `AXIOM_AUDIT.txt` is included.
- `.github/workflows/lean_action_ci.yml` has a new `ltromino` job (leanchecker and the axiom audit). `.gitignore` gains `LTromino/.lake`.
- `ROADMAP_LEDGER.md` has a new LTromino row.
- `Two_Walkers_and_a_Tick.md`:
  - §4.3 is changed from PROVED BY HAND to **VERIFIED**, with a new footnote `[^13a]` citing `universal_walker_flip_eq_sign`, the representation theorems, `one_flip_reflects_one_axis` and `both_flips_half_turn`;
  - Appendix A mentions the LTromino package;
  - the file is still **untracked and not committed**, per the 2026-10-13 instruction.
- `Downloads/For Claude Code Review/LTromino_All_Files.txt` is regenerated from the repo package, with WalkerBridge, the new lakefile, the new audit, and an update section in its BUILD_SUMMARY. The previous version is kept as `LTromino_All_Files.before_WalkerBridge.txt`.

## Problems Encountered and How They Were Fixed

- **`propext` in core `Int` lemmas.** `Int.zero_mul`, `Int.zero_add`, `Int.mul_one`, `Int.neg_mul` and `Int.mul_neg` depend on `propext` in 4.33.1. `Int.add_zero`, `Int.mul_zero`, `Int.one_mul` and `Int.neg_zero` do not.
  - I proved local `int_zero_mul'` and `int_zero_add'` by cases on `Int`.
- **Failed first proof.** The first `int_zero_mul'` closed the `negSucc` case by `rfl`. That fails because `0 * (n+1)` does not reduce for a variable `n`. It is fixed with `congrArg Int.negOfNat (Nat.zero_mul (n+1))`.
- **Self-caught weak theorem.** A first necessity statement (`product_column_misses_reflection`) did not test anything load-bearing. I replaced it with `swap_needs_exchange`: no switch has the matrix of an axis-exchanging symmetry, so the exchange is needed to realise all eight.

## What Was Tested and What Results Mean

```
lake build (in LTromino/, 12 jobs incl. SimulationExchange)   # clean, 0 warnings
lake env lean LTromino/AxiomCheck.lean                        # 170 lines, exit 0
  -> 157 "does not depend on any axioms"; all 17 WalkerBridge theorems among them
  -> the 13 exceptions are exactly the Equivariance.lean ones listed in Part 1
lake env leanchecker --fresh LTromino.{Base,Tiling,Equivariance,DiagonalBridge,WalkerBridge}   # all exit 0
forbidden-token scan (sorry|admit|native_decide|axiom|implemented_by|extern)   # no matches
```

**Scope.**
- "100% axiom-free" holds for WalkerBridge and for every module except `Equivariance.lean`. Its 13 theorems were never axiom-free and are untouched.
- §4.3's walker axes are read in the integer instructure model, the x₁ and x₂ coefficients of `Inst d₁ d₂`, the same model that grounds the §4.1 table. The footnote says so explicitly.
- The real phase torus itself (ℝ, `Int.fract`) is not part of this core-only result.

## Final State

- `LTromino/` is committed beside `SimulationExchange/`, together with the CI job, `.gitignore`, the ledger row and this summary.
- §4.3 is VERIFIED in `Two_Walkers_and_a_Tick.md` (untracked).
- Nothing has been pushed.
