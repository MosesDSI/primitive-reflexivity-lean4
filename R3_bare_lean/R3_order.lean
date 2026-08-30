namespace PrimitiveReflexivity

structure BarePartialOrder (N : Type) where
  le : N → N → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → x = y

def OrderDecorated {N : Type} (R : N → N → Prop) (ord : BarePartialOrder N) (x y : N) : Prop :=
  R x y ∧ ord.le x y

theorem a_metric_independence_order
    {N : Type}
    (R : N → N → Prop)
    (ord : BarePartialOrder N)
    (x : N) :
    OrderDecorated R ord x x ↔ R x x := by
  constructor
  · rintro ⟨hR, _⟩
    exact hR
  · intro hR
    exact ⟨hR, ord.le_refl x⟩

#print axioms a_metric_independence_order
#check @a_metric_independence_order

end PrimitiveReflexivity
