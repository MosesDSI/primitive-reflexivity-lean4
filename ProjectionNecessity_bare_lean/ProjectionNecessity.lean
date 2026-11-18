/-
  ProjectionNecessity: a finite self-reading system necessarily factors
  through a projection, which is unique, irreversible, and inherits the
  system's symmetry and handedness; the two-walker system is an instance.

  Bare Lean 4, core only (no Mathlib, no Batteries). Every declaration in
  the modules below depends on no axioms; CI enforces this with
  `axiom-audit` and an empty allowlist.

  Import order (each step imports the previous one it needs):

  * Steps 1–3: cells, feedback sees only cells, factorization.
  * Step 4a, 4b: pigeonhole, irreversibility.
  * Steps 5, 6: inherited symmetry, handedness.
  * ZeroInt: zero-axiom `Nat`/`Int` arithmetic (namespace
    `DSISVerification.ZeroInt`).
  * Steps 7a–7c: floor squeeze, parity bookkeeping, descent.
-/

import ProjectionNecessity.Step1_SameResponse
import ProjectionNecessity.Step2_FeedbackSeesOnlyCells
import ProjectionNecessity.Step3_Factorization
import ProjectionNecessity.Step4a_Pigeonhole
import ProjectionNecessity.Step4b_Irreversibility
import ProjectionNecessity.Step5_InheritedSymmetry
import ProjectionNecessity.Step6_Handedness
import ProjectionNecessity.ZeroInt
import ProjectionNecessity.Step7a_FloorSqueeze
import ProjectionNecessity.Step7b_ParityBookkeeping
import ProjectionNecessity.Step7c_Descent
