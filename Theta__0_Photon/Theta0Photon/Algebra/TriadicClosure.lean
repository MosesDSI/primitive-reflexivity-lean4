import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Triadic Closure: the 3-Component Structural Closure Failure, as a Lean Theorem

Formalizes, precisely and without overreach, the closure fact behind
`The_Classical_Statement_Deconstructed.md`'s core claim: the structure
bundling a natural number with its own square-root mediator is **not**
closed under componentwise addition. This file proves exactly that — a
statement about the specific type `TriadicNat` and the specific operation
`add_componentwise` defined below — and nothing broader. In particular, it
does **not** formalize (and does not need to, to be true) any claim about
Mathlib's `ℕ` itself failing to be closed under `+`; `ℕ` is untouched by
anything in this file.

## A build-structure note, decided explicitly rather than silently

The theorem this file drives to completion — `mediator_defect_positive` — was
proved on 2026-08-28 in `PrimitiveReflexivity/Foundations.lean`, a
*different* Lake project from this one (`Theta__0_Photon`), with no
dependency edge between them today (`Theta0Photon` only shares Mathlib with
`PrimitiveReflexivity` via a directory junction, not the compiled
`PrimitiveReflexivity` library itself). Adding a genuine cross-project Lake
dependency is a real, separate build-configuration decision — this session's
established convention is not to touch `lakefile.toml`/toolchain wiring
without it being the explicit ask, and today's ask is the theorem, not a
build restructuring. So: **`mediator_defect` and `mediator_defect_positive`
are re-derived below, verbatim in statement and proof**, rather than
imported — re-verified independently against this project's own pinned
toolchain, not merely copied and trusted. If a permanent shared dependency
is wanted later, that is worth doing deliberately, not as a side effect of
this file.

## A completed field, noted explicitly

The requested `TriadicNat` structure specifies invariants tying `axial` and
`boundary` to `n` (`h_axial`, `h_boundary`), but leaves `polar` unconstrained.
Read literally, that would make `polar` a free `ℚ` parameter disconnected
from `n` — which would mean `TriadicNat` doesn't actually bundle "a natural
number with its 3-component state" (distinct `TriadicNat` values could share
the same `n, axial, boundary` and differ only in an unrelated `polar`,
untethered to anything). Completed here with `h_polar : polar = (n : ℚ)`,
matching the evident intent and this project's own `TriadicState` structure
(`Foundations.lean`, `polar_count := (n : ℝ)`).
-/

open Polynomial

noncomputable section

/-! ## §0 — `mediator_defect`, re-derived and re-verified independently -/

/-- The additive residue in the mediator (square-root) coordinate: how far
`√n + √m` overshoots `√(n+m)`. Identical in statement to
`PrimitiveReflexivity.mediator_defect` (2026-08-28). -/
noncomputable def mediator_defect (n m : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) - Real.sqrt ((n + m : ℕ) : ℝ)

/-- **The residue is always strictly positive**, for any positive `n, m` —
re-proved here independently (same statement and proof strategy as
`PrimitiveReflexivity.mediator_defect_positive`, 2026-08-28): square both
sides of the claimed inequality, use `(√n)² = n`, `(√m)² = m`, and the
strictly positive cross term `2√n√m`, then undo the squaring via
monotonicity of `√`. -/
theorem mediator_defect_positive {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    mediator_defect n m > 0 := by
  unfold mediator_defect
  push_cast
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hm_pos
  have h_cross : 0 < 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have h_sq_n : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h_sq_m : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    positivity
  have hsum_pos : 0 < Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) := by
    have h_sq_n : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h_sq_m : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    linarith
  have h_exp : (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ^ 2
      = (n : ℝ) + (m : ℝ) + 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have h1 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
    have h2 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_nonneg
    have expand : (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ^ 2
        = (Real.sqrt (n : ℝ)) ^ 2 + (Real.sqrt (m : ℝ)) ^ 2
          + 2 * Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by ring
    rw [expand, h1, h2]
  have h_lt : Real.sqrt ((n : ℝ) + (m : ℝ)) < Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_lt' hsum_pos, h_exp]
    linarith
  linarith

/-! ## §1 — `TriadicNat`: a natural number bundled with its 3-component state -/

/-- A natural number `n`, bundled with its full 3-component triadic state
(`polar`, `axial`, `boundary`) and the invariants tying each component
exactly to `n` — `polar = n`, `axial = √n`, `boundary = n²`. -/
structure TriadicNat where
  n : ℕ
  polar : ℚ
  axial : ℝ
  boundary : ℕ
  h_polar : polar = (n : ℚ)
  h_axial : axial = Real.sqrt (n : ℝ)
  h_boundary : boundary = n * n

/-- The canonical `TriadicNat` for a given `n` — used only to confirm the
structure is genuinely inhabited for every `n`, not merely well-typed. -/
def TriadicNat.mk' (n : ℕ) : TriadicNat where
  n := n
  polar := (n : ℚ)
  axial := Real.sqrt (n : ℝ)
  boundary := n * n
  h_polar := rfl
  h_axial := rfl
  h_boundary := rfl

/-- **The raw, un-invariant-checked result of combining two `TriadicNat`
states component by component.** Each component is added in its own native
type (`ℕ` for `n`/`boundary`, `ℚ` for `polar`, `ℝ` for `axial`), not forced
through a single ambient space. Deliberately *not* itself a `TriadicNat` —
whether it can be repackaged as one is exactly what §2 answers. -/
structure TriadicCandidate where
  n : ℕ
  polar : ℚ
  axial : ℝ
  boundary : ℕ

/-- Componentwise addition of two `TriadicNat` states. -/
def add_componentwise (x y : TriadicNat) : TriadicCandidate where
  n := x.n + y.n
  polar := x.polar + y.polar
  axial := x.axial + y.axial
  boundary := x.boundary + y.boundary

/-- Componentwise multiplication of two `TriadicNat` states. -/
def mul_componentwise (x y : TriadicNat) : TriadicCandidate where
  n := x.n * y.n
  polar := x.polar * y.polar
  axial := x.axial * y.axial
  boundary := x.boundary * y.boundary

/-! ## §1b — Multiplicative closure: exact, zero residue -/

/-- **`TriadicNat` IS closed under `mul_componentwise`, on both the `axial`
and `boundary` coordinates — zero residue, not approximate.** `axial`:
`√n · √m = √(nm)` exactly (`Real.sqrt_mul`, a standard Mathlib identity, not
a new derivation — multiplication needs nothing analogous to
`mediator_defect_positive`). `boundary`: `n² · m² = (nm)²` exactly (`ring`,
unconditional on `ℕ`). -/
theorem triadic_multiplication_closed (x y : TriadicNat) :
    (mul_componentwise x y).axial = Real.sqrt ((mul_componentwise x y).n : ℝ) ∧
    (mul_componentwise x y).boundary = (mul_componentwise x y).n * (mul_componentwise x y).n := by
  constructor
  · show x.axial * y.axial = Real.sqrt (((x.n * y.n : ℕ) : ℝ))
    rw [x.h_axial, y.h_axial]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg x.n)]
  · show x.boundary * y.boundary = (x.n * y.n) * (x.n * y.n)
    rw [x.h_boundary, y.h_boundary]
    ring

/-! ## §2 — The closure failure, driven to completion by `mediator_defect_positive` -/

/-- **`TriadicNat` is not closed under `add_componentwise`.** For any two
positive-`n` states `x, y`, the componentwise sum's `axial` coordinate is
*not* `√` of its `n` coordinate — i.e. it fails exactly the `h_axial`
invariant a genuine `TriadicNat` for `x.n + y.n` would need to satisfy.
Driven to completion by `mediator_defect_positive`: the two sides of the
would-be invariant differ by exactly `mediator_defect x.n y.n`, already
proved strictly positive, hence nonzero — the structural residue forces the
`axial` component strictly off the diagonal `√(x.n+y.n)`, not merely
"probably different." -/
theorem triadic_addition_not_closed (x y : TriadicNat) (hx : x.n > 0) (hy : y.n > 0) :
    (add_componentwise x y).axial ≠ Real.sqrt ((add_componentwise x y).n : ℝ) := by
  show x.axial + y.axial ≠ Real.sqrt (((x.n + y.n : ℕ) : ℝ))
  rw [x.h_axial, y.h_axial]
  intro heq
  have hdef := mediator_defect_positive hx hy
  unfold mediator_defect at hdef
  rw [heq] at hdef
  linarith

/-! ## §3 — The projection `π`, and exactly what it discards

`π : TriadicNat → ℕ` is the flat, classical-count view: it keeps `n` and
forgets `polar`, `axial`, `boundary`. Formalized here precisely, so the two
claims about it are each pinned to an exact statement rather than left as
prose: what `π` *does* preserve (§3a — trivial, by `add_componentwise`'s own
definition), and what it discards, made into an exact number rather than an
unspecified "residue" (§3b — `mediator_defect`, restated as a correction
identity). Read together with the module docstring above: §3b is `TriadicNat`
and `mediator_defect` again, from a different angle — it is not a new,
independent result about a different mathematical object. -/

/-- The flat, classical-count projection of a `TriadicNat` — keeps `n`,
forgets everything else. -/
def π (x : TriadicNat) : ℕ := x.n

/-- `π` sees `add_componentwise` as ordinary `+` **on the `n`-coordinate
alone** — true by `add_componentwise`'s own definition (`n := x.n + y.n`),
not by any cancellation of `mediator_defect`. Stated explicitly so it is
clear this is the *only* sense in which the two operations agree. -/
theorem projection_commutes_on_n (x y : TriadicNat) :
    (add_componentwise x y).n = π x + π y := rfl

/-- **What `π` discards, made exact.** The componentwise sum's `axial`
coordinate, corrected by exactly `mediator_defect x.n y.n`, equals the
`axial` coordinate a genuine `TriadicNat` for `π x + π y` would need. The gap
between "what `add_componentwise` produces" and "what a valid `TriadicNat`
requires" is exactly this one already-positive real number — not vague
entropy, one specific quantity, already proved nonzero by
`mediator_defect_positive`. -/
theorem correction_identity (x y : TriadicNat) :
    (add_componentwise x y).axial - mediator_defect x.n y.n
      = Real.sqrt ((π x + π y : ℕ) : ℝ) := by
  show x.axial + y.axial - mediator_defect x.n y.n = Real.sqrt (((x.n + y.n : ℕ) : ℝ))
  rw [x.h_axial, y.h_axial]
  unfold mediator_defect
  ring

end
