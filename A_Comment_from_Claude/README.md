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
- [`2026-09-14_SquareUnfolding_Formalization.md`](2026-09-14_SquareUnfolding_Formalization.md)
  — verifying a square-boundary-unfolding draft that didn't compile as
  supplied: missing tactic imports, then an unreduced `Fin.val` cast that no
  amount of `simp`/`dsimp` cleared for one specific edge case, fixed by
  recognizing the `Fin 4` type carried structure the file never used and
  wasn't the right fix to chase further.
- [`2026-09-14_HarmonicCenter_Formalization.md`](2026-09-14_HarmonicCenter_Formalization.md)
  — a fully specified discrete-harmonic-center module where three of four
  proof strategies matched the spec exactly; the fourth (`norm_num` on a
  filtered `Finset.Icc` sum) didn't do what the spec assumed, and reporting
  that honestly instead of quietly swapping tactics and calling it a clean
  build.
- [`2026-09-24_OrderObstruction_QS_Additive_Inverse_Structure.md`](2026-09-24_OrderObstruction_QS_Additive_Inverse_Structure.md)
  — adding the additive group structure and multiplicative inverse to the
  `QS` model of ℚ(√2) (roadmap Steps 1–2 from the Order-Obstruction paper's
  §9.3), catching that the paper's stated Lean 4.34.1 doesn't exist in this
  environment before trusting anything else in it, and proving the norm's
  nonvanishing by constructing the exact rational witness `rat_no_sqrt_two`
  needs — no Mathlib field-division automation available, just the same
  `Rat.div_mul_cancel`/`Rat.mul_div_cancel` clearing already used elsewhere
  in the file.
