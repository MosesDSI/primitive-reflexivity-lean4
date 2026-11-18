# SimulationExchange Zero-Axiom Migration: Increments 0–2 (stopping point)

**Date:** 2026-11-18
**Branch:** `feat/simulationexchange-zero-axiom` (built on `feat/projection-necessity`; merge that one into `master` first)
**Toolchain:** `leanprover/lean4:v4.33.1`
**Resume at:** Increment 3 (`Walkers.lean`)

## Objective

Bring `SimulationExchange/` up to the "Zero-Axiom Lean 4 Verification & Hygiene
Standard" in `AGENTS.md`: every declaration with 0 axioms (empty allowlist), no
forbidden tactics, no written Nat subtraction, division or modulo, keeping
every theorem name and statement unchanged so that `LTromino/` and
`Theta__0_Photon/…/SimulationExchangeBridge.lean` need no edits.
`ProjectionNecessity_bare_lean/` stays a separate, dependency-free package.

## Decisions made by the user (all recorded in AGENTS.md)

- Statements unchanged; packages independent (SimulationExchange has its own
  `ZeroInt` copy, namespace `SimulationExchange.ZeroInt`).
- Proof invariants: Peano induction, explicit case splits, witness equations;
  no Nat subtraction, halving, `propext`, `Classical.choice`, `Quot.sound`;
  `set_option genInjectivity false` on `Inst` and any multi-field structure.
- "No Nat subtraction" means none *written*; reaching it through core's
  definitions of `Int` (`Int.add → Int.subNatNat → Nat.sub`) or of `≤`
  (`Nat.pred`) is accepted.
- ZeroInt is the one sanctioned exception to the hygiene gate (its macros use
  `simp only`; `sub_shift` states a Nat subtraction).
- `% 0` is accepted only where `IsCharP`'s field forces it: `ZeroGrind.mod_zero'`,
  `ZeroGrind.ofNat_eq_zero_of_charZero`, `Inst.instIsCharPOfNatNat`.
- The `decide` ban stands; LTromino is recorded as kernel-clean but lexically
  non-compliant (80 uses), to be fixed in a separate pass.
- Polynomial identities: a verified normalizer (`ZeroRing`), with expression
  trees written by hand (no reification tactic).

## What was done

| Commit | Content |
|---|---|
| `7836f24` | Increment 0: `ZeroInt.lean` (copy), `ZeroGrind.lean` (ring lemmas from the `Lean.Grind` class fields; `mod_zero'`; IsCharP test) |
| `0be0b53` | Scanner forbids `push_cast` and similar |
| `d6d80bb` | Increment 1a: Core §0–§2, §5–§6; new `ZeroNat.lean`; `descent` no longer well-founded |
| `79a0bd2` | Increment 1b-i: ring/cast toolkit (`intCast_add/mul/sub`, `intCast_inj`) and `ZeroRing.lean` (verified normalizer, `intCommRing`) |
| `0a7b327` | `tools/zero_axiom_natops.py` (written Nat sub/div/mod check) |
| `f94c112` | Increment 1b-ii: Core §3–§4; **Core fully zero-axiom** |
| `5feaca9` | Fix: natops now scans proof bodies (it read statements only; earlier claims re-verified and hold) |
| `35f3dac` | Increment 2: **Model (the instructure ring) zero-axiom**; `Inst.mk.injEq` removed (needs `propext`); `% 0` exception extended |
| this note | Handoff note and `SimulationExchange/migration/` (baseline + audit scripts) |

## Problems found and how they were handled

- Core Lean's derived lemmas carry axioms: `Lean.Grind.Ring.neg_mul`,
  `intCast_add`, `intCast_mul`, `IsCharP.intCast_eq_zero_iff`, `Nat.mod_zero`,
  `Nat.succ_ne_zero`, `Int.mul_eq_zero`, `List.getD` (via `Nat.bitwise`).
  Replacements live in `ZeroGrind`, `ZeroNat`, `ZeroRing`, Core.
- `ZeroRing` usage rule: expression trees must be **named top-level `def`s**.
  Inline `let` trees made a degree-4 check take more than 6 minutes; named
  ones take about 2.5 seconds. Use `atoms [...]`, never `List.getD`.
- A `rw` with `eq_of_check …` fails (the pattern is the unevaluated `eval`).
  State the identity as a `have` with its explicit type, then `rw` with it.
- The natops tool read only statements (`ConstantInfo.value?` returns `none`
  for theorems). Fixed in `5feaca9`; its self-test now has a proof-body control.
- The `@[simp]` attributes were removed from Model. The five unmigrated
  modules each carry a temporary
  `attribute [local simp] SimulationExchange.Inst.add_def …` line, which must
  be **deleted when that module is rewritten**.

## Tested (final state of `35f3dac`, fresh builds)

- `lake build`: SimulationExchange 14 jobs, LTromino 16 jobs, no warnings;
  Theta's `SimulationExchangeBridge` builds.
- Statements: 164 of 165 original signatures identical (set comparison,
  `pp.all`); the one removed is `Inst.mk.injEq`.
- Module audit (`migration/ModuleAudit.lean`), declarations with axioms:

| Module | Declarations | With axioms |
|---|---|---|
| ZeroInt | 66 | 0 |
| ZeroNat | 9 | 0 |
| ZeroGrind | 35 | 0 |
| ZeroRing | 180 | 0 |
| Core | 61 | 0 |
| Model | 91 | 0 |
| Walkers | 19 | 18 |
| Meeting | 13 | 13 |
| Boundary | 42 | 31 |
| Instances | 14 | 5 (was 11; some only inherited axioms from Core) |
| Switching | 86 | 76 |

- Hygiene (`tools/zero_axiom_hygiene.py`): 0 forbidden in all finished modules.
- natops (`tools/zero_axiom_natops.py`, proof bodies included): 0 unallowed in
  all finished modules.

## How to resume (Increment 3, Walkers)

1. Read `AGENTS.md` (the standard) and this note.
2. `cd SimulationExchange && lake build` (expect 14 jobs, no warnings).
3. Read `SimulationExchange/Walkers.lean` in full. Its 18 axiom-bearing
   declarations include `coincidence_only_at_origin`,
   `walkers_coincide_only_at_origin`, `dominance_identity`, `no_tie`,
   `dominance_never_ties` and their counterexamples (`*_needs_*`).
4. Rewrite proofs only, keeping statements. Tools: `ZeroGrind` (ring and cast
   lemmas, `intCast_inj`), `ZeroRing` (`eq_of_check` over any ring, or over Int
   via `@eq_of_check Int intCommRing …`), Core's `descent_int`,
   `int_mul_eq_zero`, `int_not_one_le_zero`. Closed numeric facts:
   `rfl` / `Nat.le_of_ble_eq_true rfl`, never `decide`.
5. Delete Walkers' temporary `attribute [local simp] …` line.
6. Run all gates, in a fresh build:
   - `lake build` (SimulationExchange) and `cd ../LTromino && lake build`
   - `lake env lean migration/ModuleAudit.lean` (Walkers must show 0)
   - signatures: `lake env lean migration/Signatures.lean | sed 's/^.*info: //' | tr -d '\r' | sort`,
     compared as a set (`comm -23`) with `tr -d '\r' < migration/signature_baseline.txt | sort`
     (expect only `Inst.mk.injEq` missing). Strip `\r` on both sides, because Git
     may check the baseline out with Windows line endings.
   - `python -I tools/zero_axiom_hygiene.py --selftest`, then on `Walkers.lean`
   - `python -I tools/zero_axiom_natops.py --selftest`, then
     `python -I tools/zero_axiom_natops.py SimulationExchange SimulationExchange.Walkers`
7. Commit, then continue: Increment 4 Meeting and Boundary, 5 Instances,
   6 Switching (largest; 56 `simp`).

## Decisions still pending

- **Boundary (Increment 4):** `AbovePos a := a % 2 = 1` and `AboveNeg` are
  definitions with a written Nat `% 2`, and `inStep_iff_D₂_even` and
  `D₁_D₂_same_parity` state `% 2` on `Int`. Statements stay unchanged, so these
  `%`s cannot be removed; the user must decide how to treat them.
- **After Switching:** switch the `simulation-exchange` CI job to the empty
  allowlist (`axiom-audit-allow: ","`, as for `ltromino`), and update
  `ROADMAP_LEDGER.md`. Its Tier 1 text calls SimulationExchange "bare-Lean"
  under "no axioms at all", which is not yet true.
- **Later, separate passes:** LTromino's 80 `decide` uses; optionally a CI step
  for the hygiene and natops tools.
- **Not pushed before this session ended:** see the final push in this
  session's log. `feat/projection-necessity` must be merged before
  `feat/simulationexchange-zero-axiom`.
