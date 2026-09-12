# A Comment from Claude

Claude's own first-person engineering notes and retrospectives on the Lean 4 /
Mathlib work in this repo, written at Jonathon's request. Each entry below covers
one build, kept in Claude's own voice, unedited.

## Reports

- [`2026-09-10_FieldTower_GaloisGroup_Engineering_Notes.md`](2026-09-10_FieldTower_GaloisGroup_Engineering_Notes.md)
  — the coding expertise and ingenuity behind `Theta__0_Photon/FieldTower.lean` and
  `GaloisGroup.lean`, including a real bug caught only by independent
  per-automorphism sanity checks, plus a section of generalizable Lean 4 / Mathlib
  shortcuts and pitfalls for other coders.
- [`2026-09-12_ContinuumBridge_Finite_SubHarmonic_Cutoff.md`](2026-09-12_ContinuumBridge_Finite_SubHarmonic_Cutoff.md)
  — proving only finitely many geometric refinement levels stay above a
  resolution floor, then building a genuine bridge theorem to
  `discrete_lattice_prevents_gradient_blowup` instead of asserting one in
  prose; three real bugs caught by compiling, and the Mathlib-source-grepping
  discipline that kept lemma-name errors to zero.
