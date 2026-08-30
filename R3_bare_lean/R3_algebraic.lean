namespace PrimitiveReflexivity

class BareMonoid (M : Type) where
  op : M → M → M
  zero : M
  op_zero (x : M) : op x zero = x

def AlgebraicDecorated {N M : Type} [BareMonoid M]
    (R : N → N → Prop) (extra : N → M) (x y : N) : Prop :=
  R x y ∧ (BareMonoid.op (extra x) BareMonoid.zero = extra x)

theorem a_metric_independence_algebraic
    {N M : Type}
    [m : BareMonoid M]
    (R : N → N → Prop)
    (extra : N → M)
    (x : N) :
    AlgebraicDecorated R extra x x ↔ R x x := by
  constructor
  · rintro ⟨hR, _⟩
    exact hR
  · intro hR
    constructor
    · exact hR
    · exact BareMonoid.op_zero (extra x)

#print axioms a_metric_independence_algebraic
#check @a_metric_independence_algebraic

end PrimitiveReflexivity
