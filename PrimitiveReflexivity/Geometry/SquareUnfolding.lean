import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimitiveReflexivity.Geometry

/-!
# Discrete Square Unfolding Formalization
Models the boundary metric of a square [0, s] × [0, s], its canonical unfolding
into the interval [0, 4s], and isometric preservation of edge lengths.
-/

/-- The four cyclic directed edges comprising the boundary of a 2D square. -/
inductive SquareEdge : Type
  | bottom : SquareEdge -- (0,0) -> (s,0)
  | right  : SquareEdge -- (s,0) -> (s,s)
  | top    : SquareEdge -- (s,s) -> (0,s)
  | left   : SquareEdge -- (0,s) -> (0,0)
  deriving DecidableEq, Repr

/-- Cyclic index of each boundary edge in order of traversal. -/
def SquareEdge.index : SquareEdge → ℕ
  | .bottom => 0
  | .right  => 1
  | .top    => 2
  | .left   => 3

/-- Unfolded base offset for each edge along the linear interval [0, 4s]. -/
def edgeOffset (s : ℝ) (e : SquareEdge) : ℝ :=
  (e.index : ℝ) * s

/-- Point parameterization along the square boundary:
    Takes an edge and an internal edge coordinate `t ∈ [0, s]`. -/
structure BoundaryPoint (s : ℝ) where
  edge : SquareEdge
  t : ℝ
  h_nonneg : 0 ≤ t
  h_le : t ≤ s

/-- Canonical unfolding map: embeds the boundary point into ℝ. -/
def unfoldPoint {s : ℝ} (p : BoundaryPoint s) : ℝ :=
  edgeOffset s p.edge + p.t

/-- Total perimeter length of the unfolded square. -/
def squarePerimeter (s : ℝ) : ℝ := 4 * s

/-- Lemma 1: The unfolding map of any boundary point lies strictly within [0, 4s]. -/
theorem unfold_bounds {s : ℝ} (hs : 0 ≤ s) (p : BoundaryPoint s) :
    0 ≤ unfoldPoint p ∧ unfoldPoint p ≤ squarePerimeter s := by
  dsimp [unfoldPoint, edgeOffset, squarePerimeter]
  cases p.edge
  all_goals
    norm_num [SquareEdge.index]
    constructor
    · linarith [p.h_nonneg]
    · linarith [p.h_le]

/-- Lemma 2: Isometric preservation of segment lengths under unfolding.
    Internal displacement along an edge matches linear distance in ℝ. -/
theorem unfold_isometry_same_edge {s : ℝ} (e : SquareEdge)
    (t₁ t₂ : ℝ) (h₁ : 0 ≤ t₁) (h₁' : t₁ ≤ s) (h₂ : 0 ≤ t₂) (h₂' : t₂ ≤ s) :
    unfoldPoint ⟨e, t₂, h₂, h₂'⟩ - unfoldPoint ⟨e, t₁, h₁, h₁'⟩ = t₂ - t₁ := by
  dsimp [unfoldPoint]
  ring

/-- Lemma 3: Corner Continuity / Glue Invariant.
    The terminal vertex of edge `i` unfolds to the exact initial offset of edge `i+1`. -/
theorem unfold_corner_adjacency (s : ℝ) :
    edgeOffset s .bottom + s = edgeOffset s .right ∧
    edgeOffset s .right + s = edgeOffset s .top ∧
    edgeOffset s .top + s = edgeOffset s .left := by
  dsimp [edgeOffset, SquareEdge.index]
  refine ⟨by ring, by ring, by ring⟩

/-- Theorem: Global Conservation of Perimeter under Complete Unfolding. -/
theorem perimeter_unfold_conservation (s : ℝ) :
    edgeOffset s .left + s = squarePerimeter s := by
  dsimp [edgeOffset, SquareEdge.index, squarePerimeter]
  ring

end PrimitiveReflexivity.Geometry
