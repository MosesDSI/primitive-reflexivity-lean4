import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Testing "Exact Multiplicative Closure + Positive Additive Residue"

The claim tested here: `f(n) = √n` satisfies, simultaneously, (a)
`f(n)·f(m) = f(nm)` exactly, and (b) `f(n)+f(m) > f(n+m)` strictly, for
positive `n, m`.

## A correction to this file's own earlier content

An earlier version of this file also carried an `n³` "counterexample". On
inspection, that theorem proved `n³+m³-(n+m)³ ≠ 0` — and in fact strictly
*negative* — which is the opposite sign from condition (b) above, which
requires a strictly *positive* residue. `n³` does not satisfy (a) ∧ (b) as
stated, so it was never a valid counterexample to a claim built from those
two conditions; it has been removed rather than left misdescribed.

## What remains: the constant function

The constant function `f(n) = 1` does satisfy (a) and (b) exactly, literally,
as stated (`1·1=1`; `1+1-1=1>0`), for every `n, m`. This is a real fact about
those two conditions taken alone, with no positivity hypothesis on `n, m`
even needed.

**Read in the framework's own terms, this is a degenerate, scale-collapsed
case**: the constant `1` carries no dependence on `n` at all, so it cannot
serve as an axial mediator in the triadic sense — it has no capacity to
track phase drift, scaling variance, or the continuous rotation between
number-states that `√n` provides. It is not offered here as an interesting
rival mediator on par with `√n`, only as a literal witness that (a) ∧ (b)
alone, without an explicit non-degeneracy/dependence-on-`n` clause, do not
by themselves rule it out. Adding such a clause is a legitimate, explicit
strengthening of the framework's criteria — not something (a) ∧ (b) already
encode on their own.
-/

/-- Condition (a) for `f = fun _ => (1:ℝ)`: exact multiplicative closure. -/
theorem const_one_multiplicative_closure (_n _m : ℕ) :
    (1 : ℝ) * (1 : ℝ) = (1 : ℝ) := by norm_num

/-- Condition (b) for `f = fun _ => (1:ℝ)`: strictly positive additive
residue — unconditionally, no positivity hypothesis on `n, m` even needed. -/
theorem const_one_additive_residue (_n _m : ℕ) :
    (1 : ℝ) + (1 : ℝ) - (1 : ℝ) > 0 := by norm_num

/-- **Both conditions (a) and (b) hold, literally, for the constant
function.** As the module docstring states plainly: this is a degenerate,
scale-collapsed point, not a claim that `1` is a meaningful rival to `√n` as
a mediator — a mediator locked to a constant value carries no operational
scaling capacity. -/
theorem const_one_satisfies_both_conditions :
    (∀ _n _m : ℕ, (1:ℝ) * (1:ℝ) = (1:ℝ)) ∧
    (∀ _n _m : ℕ, (1:ℝ) + (1:ℝ) - (1:ℝ) > 0) :=
  ⟨const_one_multiplicative_closure, const_one_additive_residue⟩
