structure Node where
  id : Nat

def R (x y : Node) : Prop := x = y

structure NodeMetric (N : Type) where
  dist : N → N → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

def Process := ∀ x : Node, R x x

def MetricDecorated (R : Node → Node → Prop) (M : NodeMetric Node)
    (P : Nat → Prop) (x y : Node) : Prop :=
  R x y ∧ P (M.dist x y)

/-- Two nodes are off-diagonal when they are not related by `R` (concretely,
when they are not equal). -/
def OffDiagonal (x y : Node) : Prop := ¬ R x y

/-- A metric is strict when every off-diagonal pair has strictly positive
distance: the usual "distinct points are not zero apart" requirement of a
genuine (as opposed to merely pseudo-) metric. This is kept separate from
`NodeMetric` itself, rather than added as a field, so `zero_is_not_a_coordinate`
keeps holding for any metric, strict or not. -/
def NodeMetric.Strict (M : NodeMetric Node) : Prop :=
  ∀ x y, OffDiagonal x y → 0 < M.dist x y

/-- Under a strict metric, no off-diagonal pair can have zero distance. -/
theorem off_diagonal_dist_ne_zero {M : NodeMetric Node} (hM : M.Strict)
    {x y : Node} (hxy : OffDiagonal x y) : M.dist x y ≠ 0 := by
  have h := hM x y hxy
  omega

/-- A strict metric's zero-distance pairs are exactly the diagonal: distance
zero holds if and only if the relation `R` already holds. Metric decorations
therefore only ever carry non-trivial (nonzero) information strictly outside
the diagonal; on it, and only on it, the metric contributes nothing beyond
what `R` already says. -/
theorem dist_eq_zero_iff_R {M : NodeMetric Node} (hM : M.Strict) (x y : Node) :
    M.dist x y = 0 ↔ R x y := by
  constructor
  · intro h0
    exact Classical.byContradiction fun hne => off_diagonal_dist_ne_zero hM hne h0
  · intro hR
    have hxy : x = y := hR
    rw [hxy]
    exact M.dist_self y
