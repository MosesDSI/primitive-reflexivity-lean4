variable {N : Type}

theorem a_metric_independence
    (R : N → N → Prop) (M : Type) (extra : N → N → M) :
    ∀ x : N, R x x ↔ R x x := by
  intro x
  rfl

#print axioms a_metric_independence
#check @a_metric_independence
