# AGENTS.md

## Purpose

This file provides context and evaluation criteria for human and automated reviewers.

It is not a request for positive reviews or an attempt to restrict criticism.
Its purpose is to make reviews relevant, accurate, and aligned with the stated
goals of this project.

This repository is a formal-mathematics research artifact, not an application,
conventional software library, or product. Review its structure, files, and
verification tiers accordingly.

## What This Repository Is

- A Lean 4 and Mathlib formalization of the Primitive Reflexivity ontology and
  selected derived theorems.
- A research artifact containing:
  - kernel-checked theorem statements and proofs
  - axiom audits
  - bare-Lean verification tiers
  - Mathlib-based formalization
  - build summaries and adjustment logs

The correctness of a formalized theorem statement is checked by Lean's kernel,
relative to Lean's trusted base and its imported dependencies. This does not,
by itself, establish every broader conceptual, mathematical, physical, or
interpretive claim associated with the formalization.

## What This Repository Is Not

- An application
- A conventional software library
- A package primarily intended for API consumption
- A system whose primary evidence is runtime behavior

The absence of unit tests, examples, API documentation, or application code is
not, by itself, a negative finding for this kind of research artifact.

## How To Interpret The Repository

Treat the following as distinct evidence sources with different scopes:

- **Bare-Lean modules**
  Dependency-free proofs checked directly by the Lean kernel.

- **Mathlib modules**
  Kernel-checked proofs that rely on Mathlib definitions and lemmas, and may
  have a broader reported axiom or trust base.

- **Build logs**
  Evidence that specified commands succeeded in a stated environment. They
  support reproducibility claims but do not alone establish reproducibility in
  every environment.

- **Axiom audits**
  Evidence of the axioms reported for individual declarations.

- **Documentation files**
  Statements of conceptual intent, theorem provenance, structural rationale,
  and the claims against which the formalization should be compared.

Do not collapse these layers into a single generic "project completeness"
metric.

### Axiom-audit scope: theorems versus declarations

A `#print axioms` list built from a module's `theorem` lines covers only the
theorems written in the source. It does not cover declarations the compiler
synthesizes, such as a structure's `mk.injEq` lemma, which depends on
`propext`. The environment-wide `axiom-audit` tool, run by CI, checks every
declaration under a library root. When a claim says "no axioms", check which
of the two scopes it refers to.

`LTromino/` claims no axioms at both scopes, and CI enforces this:

- The `ltromino` CI job runs `axiom-audit` with `axiom-audit-allow: ","`.
  This is the empty allowlist: the tool drops blank entries, and a bare `""`
  could be replaced by the action's default. Do not remove it or widen it.
- `Sym`, `Tromino` and `WalkerMatrix` are declared with
  `set_option genInjectivity false`. Lean's auto-generated `mk.injEq` uses
  `propext`, so this option is load-bearing. As a consequence, proofs cannot
  use `mk.inj` or `mk.injEq` for these structures.
- `LTromino/LTromino/AxiomCheck.lean` (theorem scope) is a complement to the
  CI audit, not a substitute for it.
- Full account: `docs/notes/LTromino_Axiom_Audit_Scope_and_CI_Enforcement.md`.

## Zero-Axiom Lean 4 Verification & Hygiene Standard

All Lean 4 proofs, libraries, and verification scripts in this repository must adhere to strict zero-axiom compliance (`0 axioms`, `0 sorrys`, `0 warnings`).

### 1. Kernel-Level Axiom Gate (Ground Truth)
- **Mandatory `#print axioms` Check:** Every exported theorem and lemma must be verified via `#print axioms <DeclarationName>` in a clean-room check file (or `leanchecker --fresh` / `axiom-audit` with an empty allowlist).
- **Zero Tolerance for Standard Axioms:** Any dependency on `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or `sorryAx` is an immediate verification failure.
- **Prevent Implicit Axiom Generation:** On inductive types where compiler-generated `.injEq` lemmas pull in `propext`, explicitly set `set_option genInjectivity false` and prove injectivity constructively.

### 2. Source-Level Lexical Hygiene Gate (Second Line of Defense)
- **Ban Line-Level Exclusion Filters (`grep -v`):** Never use `grep -v` or any whole-line exclusion filter to suppress false positives. Discarding an entire line because it contains a safe prefix (e.g., `ZeroGrind.` or `Lean.Grind.`) blinds the check to forbidden tokens appended later on that same line.
- **Require Stateful Lexer-Aware Scanning:** Source scans must strip nested block comments (`/- ... -/`), line comments (`--`), and string literals (`"..."`) prior to pattern matching.
- **Token-Level Matching Only:** Match forbidden identifiers and automation tactics (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`, `implemented_by`, `extern`, `grind`, `omega`, `simp`, `decide`, `native_decide`, `linarith`, `ring`, `norm_num`, `Classical`, `Quot`) strictly as standalone lexical tokens, case-sensitively, without line suppression.
- **Flag Semantic Hazard Operators:** Any non-commented binary `-` (saturating `Nat` subtraction), `/` (floor division), or `%` (modulo) must be flagged for manual review to ensure no silent truncation or division-by-zero totality assumptions enter discrete proofs.

### 3. Reporting Invariant
- Never claim a file or proof is "zero-axiom verified" until both the **Lexer-Aware Hygiene Scan** (0 unreviewed violations) and the **Kernel `#print axioms` Audit** pass on a fresh `lake build`.

### Scope, tools and settled interpretations

- **Scope.** The standard governs the zero-axiom packages
  (`ProjectionNecessity_bare_lean/`, `LTromino/`, and `SimulationExchange/`,
  whose migration is in progress) and all new bare-Lean work. Mathlib-tier
  modules (`Theta__0_Photon/`, `PrimitiveReflexivity/`) keep their declared
  trust base, as described under "How To Interpret The Repository"; do not
  report their standard axioms as failures of this standard.
- **Known non-compliance: `LTromino/` (recorded 2026-11-18).** LTromino
  passes the kernel gate (CI `axiom-audit`, empty allowlist, 0 axioms on all
  declarations) but fails the lexical gate: it uses `decide` 80 times on
  closed finite goals (`Base.lean` 38, `DiagonalBridge.lean` 14,
  `Equivariance.lean` 11, `WalkerBridge.lean` 9, `Tiling.lean` 8). The ban on
  `decide` stands. These uses are to be rewritten in a separate pass. Until
  then, do not describe LTromino as compliant with this standard; "0 axioms
  (kernel gate)" remains accurate.
- **Scanner.** `tools/zero_axiom_hygiene.py` implements Section 2. Run
  `python -I tools/zero_axiom_hygiene.py --selftest` first (it must pass on
  its planted fixture), then `python -I tools/zero_axiom_hygiene.py <files>`.
  Exit status 1 means a forbidden token; every REVIEW line must be checked by
  hand and the outcome stated in the report.
- **Written Nat operations.** `tools/zero_axiom_natops.py` mechanically
  checks every declaration's elaborated term for Nat `-`, `/`, `%` and
  `Nat.sub`/`Nat.pred`/`Nat.div`/`Nat.mod`. Run `--selftest` first (positive
  control: it must detect ZeroInt's `sub_shift`), then
  `python -I tools/zero_axiom_natops.py PACKAGE_DIR ROOT [--allow DECL ...]`.
  Only the accepted exceptions below may be passed to `--allow`.
- **Nat subtraction (decided 2026-11-18).** "No Nat subtraction" means no
  *written* Nat `-`, `/`, `Nat.sub` or `Nat.pred` in proofs or statements.
  Core Lean's own definitions reach them: `Int.add → Int.subNatNat →
  Nat.sub`, and `Nat.le_of_succ_le_succ → Nat.pred`. Reaching them only
  through those core definitions is accepted, and a dependency trace should
  record it.
- **ZeroInt exception (decided 2026-11-18).** `ZeroInt.lean` (the copies in
  `ProjectionNecessity_bare_lean/` and `SimulationExchange/`) is the one
  sanctioned exception to Section 2. Its `nat_ring` / `int_ring` macros use
  `simp only`, and its `sub_shift` states a Nat subtraction because core's
  `Int.subNatNat` is defined by one. All of it is axiom-free. No other file
  may call its macros; other files use its proved lemmas by name.
- **Reviewed `%` exception (decided 2026-11-18).**
  `SimulationExchange/SimulationExchange/ZeroGrind.lean`'s `mod_zero'` states
  `x % 0 = x`, the division-by-zero convention, and unfolds `Nat.mod` to
  prove it. It is accepted because core's `Lean.Grind.IsCharP` defines
  characteristic `p` through its only field,
  `ofNat_ext_iff : OfNat.ofNat x = OfNat.ofNat y ↔ x % p = y % p`, so
  `[IsCharP R 0]` can only be read through `% 0`. This is the only permitted
  `%`. It is confined to that reading, and its three REVIEW lines in the
  scanner output are expected.

## Relevant Evaluation Criteria

Evaluate:

- Whether theorem statements match their formalized proofs
- Whether definitions are coherent and used consistently
- Whether the verification tier, bare Lean or Mathlib, is correctly declared
- Whether axiom audits match claims made in documentation
- Whether build instructions reproduce the stated results
- Whether definitions and theorems compose consistently
- Whether a mismatch exists between the paper's claims and the formalization
- Whether a paper claim is broader than the corresponding Lean statement

These criteria are falsifiable, domain-appropriate, and aligned with the
project's goals.

## Irrelevant Default Heuristics

Do not treat the following as negative findings without a concrete connection
to a stated project goal:

- Absence of unit tests
- Absence of examples
- Absence of API documentation
- Absence of application code
- Absence of runtime behavior
- Assumptions that an abstraction is incomplete without its documented context
- Departure from conventional software-library structure

Examples, documentation, and reproduction instructions may still be useful for
accessibility and auditability; their absence is simply not an automatic defect.

## Useful Criticism

Useful criticism is specific, falsifiable, grounded in the repository's stated
aims, and based on a concrete mismatch.

Examples:

- "The documentation claims X, but the formal theorem proves Y."
- "This axiom audit includes `Classical.choice`, but the documentation claims
  that it does not."
- "This definition conflicts with the ontology described in the README."
- "This proof uses a stronger lemma than the paper's stated argument requires."
- "The paper makes a broader mathematical or physical claim than the current
  Lean statement formalizes."

## Non-Responsive Criticism

The following are not useful findings unless tied to a concrete project goal:

- "This project has no tests."
- "This codebase lacks examples or API docs."
- "This abstraction looks incomplete without additional methods."
- "This repository does not contain application logic."
- "This project does not follow typical software-library conventions."

## Summary

> Evaluate this repository as a formal-mathematics research artifact.
>
> Review formal claims at their declared verification tier.
>
> Distinguish kernel-checked theorem statements from conceptual interpretation.
>
> Assess how definitions and theorems compose before judging an individual
> abstraction in isolation.
>
> Report concrete, falsifiable mismatches between claims and formalization.
>
> Do not apply generic software-project heuristics as default negative findings.
