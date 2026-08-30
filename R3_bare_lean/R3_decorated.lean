variable {N M : Type}

def Decorated (R : N → N → Prop) (extra : N → N → M) (P : M → Prop) (x y : N) : Prop :=
  R x y ∧ P (extra x y)

theorem a_metric_independence_v2
    (R : N → N → Prop) (extra : N → N → M) (P : M → Prop)
    (hgate : ∀ x, P (extra x x)) :
    ∀ x, Decorated R extra P x x ↔ R x x := by
  intro x
  unfold Decorated
  constructor
  · intro h
    exact h.1
  · intro hr
    exact ⟨hr, hgate x⟩

#print axioms a_metric_independence_v2
#check @a_metric_independence_v2
