/-
  Projection Necessity, Step 6: handedness.

  Bare Lean 4. Imports only Step 5 of this folder (which imports Step 3).
  Proofs are terms built from `Eq.refl`, `Eq.symm`, `Eq.trans`,
  `congrArg` and pattern matching. No tactics. Target: zero axioms for
  every declaration.

  Setting. The responses carry an involution `τ` (`τ (τ y) = y`), such as
  swapping `above` and `below`. A symmetry `σ` of the states has a hand:

  * `keep`: it leaves every response unchanged, `r (σ φ) = r φ`.
  * `reverse`: it mirrors every response, `r (σ φ) = τ (r φ)`.

  For the walkers: the Phantom Middle keeps the in-step bit and each
  single flip reverses it (`phantom_middle_preserves_inStep`).

  Conclusions:

  * `hasHand_comp`: hands compose like signs. Reverse after reverse is
    keep; keep is neutral. This is the shape of the chiral sign law
    `det(σM) = sign(σ)·det(M)` (§11.7 of the Verified Edition).
  * `reverse_reverse_project_invariant`: two reversing symmetries in a
    row leave the projection invariant, through Step 5.
  * `reverse_moves_every_cell`: if `τ` fixes no response that occurs
    (no state is "on the wall"), a reversing symmetry moves every cell.
    Handedness is then visible in the projection, not only in `r`.
  * `hand_well_defined`: under the same condition, no symmetry is both
    keeping and reversing (unless there are no states at all). The hand
    of a symmetry is a definite property.
-/

import ProjectionNecessity.Step5_InheritedSymmetry

namespace PrimitiveReflexivity.ProjectionNecessity

/-- The two hands of a symmetry. -/
inductive Hand : Type where
  | keep : Hand
  | reverse : Hand

/-- Hands compose like signs: `keep` is neutral and two `reverse`s make
a `keep`. -/
def Hand.mul : Hand → Hand → Hand
  | Hand.keep, h => h
  | Hand.reverse, Hand.keep => Hand.reverse
  | Hand.reverse, Hand.reverse => Hand.keep

/-- What a hand does to a response: `keep` leaves it, `reverse` applies
the involution `τ`. -/
def twist {R : Type} (τ : R → R) : Hand → R → R
  | Hand.keep, y => y
  | Hand.reverse, y => τ y

/-- `τ` undoes itself, like swapping `above` and `below`. -/
def Involution {R : Type} (τ : R → R) : Prop :=
  ∀ y : R, τ (τ y) = y

/-- **Twisting twice is twisting by the product of the hands.** -/
theorem twist_mul {R : Type} {τ : R → R} (hτ : Involution τ) :
    ∀ (h₁ h₂ : Hand) (y : R),
      twist τ h₁ (twist τ h₂ y) = twist τ (Hand.mul h₁ h₂) y
  | Hand.keep, _, _ => rfl
  | Hand.reverse, Hand.keep, _ => rfl
  | Hand.reverse, Hand.reverse, y => hτ y

/-- **The hand of a symmetry.** `σ` has hand `h` when it acts on every
response by `twist τ h`. -/
def HasHand {Φ R : Type} (r : Φ → R) (τ : R → R) (σ : Φ → Φ) (h : Hand) :
    Prop :=
  ∀ φ : Φ, r (σ φ) = twist τ h (r φ)

/-- **Hands compose like signs.** Doing `σ₂` and then `σ₁` has the
product of their hands. -/
theorem hasHand_comp {Φ R : Type} {r : Φ → R} {τ : R → R}
    (hτ : Involution τ) {σ₁ σ₂ : Φ → Φ} {h₁ h₂ : Hand}
    (hs₁ : HasHand r τ σ₁ h₁) (hs₂ : HasHand r τ σ₂ h₂) :
    HasHand r τ (fun φ => σ₁ (σ₂ φ)) (Hand.mul h₁ h₂) :=
  fun φ =>
    Eq.trans (hs₁ (σ₂ φ))
      (Eq.trans (congrArg (twist τ h₁) (hs₂ φ)) (twist_mul hτ h₁ h₂ (r φ)))

/-- A reversing symmetry is a symmetry in the sense of Step 5, with `τ`
acting on responses. -/
theorem reverse_equivariant {Φ R : Type} {r : Φ → R} {τ : R → R}
    {σ : Φ → Φ} (hs : HasHand r τ σ Hand.reverse) : Equivariant r σ τ :=
  hs

/-- **Two reversals leave the projection invariant.** -/
theorem reverse_reverse_project_invariant {Φ R : Type} {r : Φ → R}
    {τ : R → R} (hτ : Involution τ) {σ₁ σ₂ : Φ → Φ}
    (hs₁ : HasHand r τ σ₁ Hand.reverse) (hs₂ : HasHand r τ σ₂ Hand.reverse)
    (φ : Φ) : project r (σ₁ (σ₂ φ)) = project r φ :=
  project_invariant (hasHand_comp hτ hs₁ hs₂) φ

/-- **No state on the wall.** `τ` changes the response of every state. -/
def OffTheWall {Φ R : Type} (r : Φ → R) (τ : R → R) : Prop :=
  ∀ φ : Φ, τ (r φ) ≠ r φ

/-- **A reversing symmetry moves every cell.** If no state is on the
wall, a reversing symmetry sends every state to a different cell. -/
theorem reverse_moves_every_cell {Φ R : Type} {r : Φ → R} {τ : R → R}
    (hwall : OffTheWall r τ) {σ : Φ → Φ}
    (hs : HasHand r τ σ Hand.reverse) (φ : Φ) :
    project r (σ φ) ≠ project r φ :=
  fun heq => hwall φ (Eq.trans (Eq.symm (hs φ)) (congrArg Subtype.val heq))

/-- **The hand is well defined.** If no state is on the wall, a symmetry
that both keeps and reverses would leave no state at all. -/
theorem hand_well_defined {Φ R : Type} {r : Φ → R} {τ : R → R}
    (hwall : OffTheWall r τ) {σ : Φ → Φ}
    (hkeep : HasHand r τ σ Hand.keep) (hrev : HasHand r τ σ Hand.reverse)
    (φ : Φ) : False :=
  hwall φ (Eq.trans (Eq.symm (hrev φ)) (hkeep φ))

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.twist_mul
#print axioms PrimitiveReflexivity.ProjectionNecessity.hasHand_comp
#print axioms PrimitiveReflexivity.ProjectionNecessity.reverse_equivariant
#print axioms PrimitiveReflexivity.ProjectionNecessity.reverse_reverse_project_invariant
#print axioms PrimitiveReflexivity.ProjectionNecessity.reverse_moves_every_cell
#print axioms PrimitiveReflexivity.ProjectionNecessity.hand_well_defined
