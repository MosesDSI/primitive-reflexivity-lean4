variable {N : Type}

structure Metric (N : Type) where
  dist : N → N → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

def MetricDecorated (R : N → N → Prop) (d : Metric N) (P : Nat → Prop) (x y : N) : Prop :=
  R x y ∧ P (d.dist x y)

theorem metric_independence
    (R : N → N → Prop) (d : Metric N) (P : Nat → Prop)
    (hgate0 : P 0) :
    ∀ x, MetricDecorated R d P x x ↔ R x x := by
  intro x
  unfold MetricDecorated
  rw [d.dist_self x]
  constructor
  · intro h
    exact h.1
  · intro hr
    exact ⟨hr, hgate0⟩

#print axioms metric_independence
#check @metric_independence
