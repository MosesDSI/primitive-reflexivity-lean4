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
