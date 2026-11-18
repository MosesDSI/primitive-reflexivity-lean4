/-
  Projection Necessity, Step 4a: the pigeonhole principle, by hand.

  Bare Lean 4, no imports. Allowed tactics are structural only: `intro`,
  `cases`, `exact`, `obtain`, `refine`, `rw`, `show`. No `simp`, `omega`,
  `decide` or `by_cases`, which can bring in `propext` or classical logic.
  Every case split on equality goes through `Nat.decEq`, a constructive
  decision procedure. Target: zero axioms for every declaration.

  Statement. Number the states `0, 1, …, k` (that is `k + 1` states) and
  let every one of them receive a response below `k` (at most `k`
  responses). Then two different states receive the same response.

  This is the counting fact behind irreversibility: when there are more
  states than responses, some cell must contain two distinct states.
  Step 4b applies it to the projection of Step 3.

  Proof outline, by induction on `k`.
  * `k = 0`: no response is below `0`, so the hypothesis already fails.
  * `k + 1`: look for a state `i ≤ k` with the same response as state
    `k + 1` (`bounded_search`). If one exists, that is the collision.
    If none does, response `k` can be freed: every state whose response
    is `k` is sent instead to the response of state `k + 1`
    (`swapTop`). This gives `k + 1` states with responses below `k`, so
    the induction hypothesis gives a collision, which is shown to be a
    collision of the original responses.
-/

namespace PrimitiveReflexivity.ProjectionNecessity

/-- Below `k + 1` and not equal to `k` means below `k`. -/
theorem lt_of_lt_succ_of_ne {a k : Nat} (h : a < k + 1) (hne : a ≠ k) :
    a < k :=
  Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hne

/-- **Bounded search.** Either some state `i ≤ k` has response `c`, or
none does. Constructive: decided by `Nat.decEq`, one state at a time. -/
theorem bounded_search (f : Nat → Nat) (c : Nat) :
    ∀ k : Nat, (∃ i, i ≤ k ∧ f i = c) ∨ (∀ i, i ≤ k → f i ≠ c)
  | 0 => by
    cases Nat.decEq (f 0) c with
    | isTrue h => exact Or.inl ⟨0, Nat.le_refl 0, h⟩
    | isFalse h =>
      refine Or.inr ?_
      intro i hi
      rw [Nat.eq_zero_of_le_zero hi]
      exact h
  | k + 1 => by
    cases bounded_search f c k with
    | inl hfound =>
      obtain ⟨i, hi, hfi⟩ := hfound
      exact Or.inl ⟨i, Nat.le_succ_of_le hi, hfi⟩
    | inr hnone =>
      cases Nat.decEq (f (k + 1)) c with
      | isTrue h => exact Or.inl ⟨k + 1, Nat.le_refl (k + 1), h⟩
      | isFalse h =>
        refine Or.inr ?_
        intro i hi
        cases Nat.lt_or_eq_of_le hi with
        | inl hlt => exact hnone i (Nat.le_of_lt_succ hlt)
        | inr heq =>
          rw [heq]
          exact h

/-- Free up response `k`: a state whose response is `k` is sent to the
response of state `k + 1`; every other state keeps its response. -/
def swapTop (f : Nat → Nat) (k : Nat) (n : Nat) : Nat :=
  if f n = k then f (k + 1) else f n

/-- **Pigeonhole.** If the `k + 1` states `0, …, k` all have responses
below `k`, two different states have the same response. -/
theorem pigeonhole :
    ∀ (k : Nat) (f : Nat → Nat), (∀ n, n ≤ k → f n < k) →
      ∃ i j, i < j ∧ j ≤ k ∧ f i = f j
  | 0, f, hf => absurd (hf 0 (Nat.le_refl 0)) (Nat.not_lt_zero (f 0))
  | k + 1, f, hf => by
    cases bounded_search f (f (k + 1)) k with
    | inl hfound =>
      -- Some earlier state shares the response of state `k + 1`.
      obtain ⟨i, hi, hfi⟩ := hfound
      exact ⟨i, k + 1, Nat.lt_succ_of_le hi, Nat.le_refl (k + 1), hfi⟩
    | inr hnone =>
      -- No earlier state shares it: free up response `k` and recurse.
      have hg : ∀ n, n ≤ k → swapTop f k n < k := by
        intro n hn
        cases Nat.decEq (f n) k with
        | isTrue hfn =>
          show (if f n = k then f (k + 1) else f n) < k
          rw [if_pos hfn]
          exact lt_of_lt_succ_of_ne (hf (k + 1) (Nat.le_refl (k + 1)))
            (fun htop => hnone n hn (Eq.trans hfn (Eq.symm htop)))
        | isFalse hfn =>
          show (if f n = k then f (k + 1) else f n) < k
          rw [if_neg hfn]
          exact lt_of_lt_succ_of_ne (hf n (Nat.le_succ_of_le hn)) hfn
      obtain ⟨i, j, hij, hjk, hgij⟩ := pigeonhole k (swapTop f k) hg
      have hik : i ≤ k := Nat.le_of_lt (Nat.lt_of_lt_of_le hij hjk)
      refine ⟨i, j, hij, Nat.le_succ_of_le hjk, ?_⟩
      cases Nat.decEq (f i) k with
      | isTrue hi =>
        cases Nat.decEq (f j) k with
        | isTrue hj =>
          -- Both had response `k`.
          exact Eq.trans hi (Eq.symm hj)
        | isFalse hj =>
          -- Would make state `j ≤ k` share the response of `k + 1`.
          have h1 : swapTop f k i = f (k + 1) := if_pos hi
          have h2 : swapTop f k j = f j := if_neg hj
          exact absurd (Eq.symm (Eq.trans (Eq.trans (Eq.symm h1) hgij) h2))
            (hnone j hjk)
      | isFalse hi =>
        cases Nat.decEq (f j) k with
        | isTrue hj =>
          -- Would make state `i ≤ k` share the response of `k + 1`.
          have h1 : swapTop f k i = f i := if_neg hi
          have h2 : swapTop f k j = f (k + 1) := if_pos hj
          exact absurd (Eq.trans (Eq.symm h1) (Eq.trans hgij h2))
            (hnone i hik)
        | isFalse hj =>
          -- Neither had response `k`, so the responses were unchanged.
          have h1 : swapTop f k i = f i := if_neg hi
          have h2 : swapTop f k j = f j := if_neg hj
          exact Eq.trans (Eq.symm h1) (Eq.trans hgij h2)

end PrimitiveReflexivity.ProjectionNecessity

#print axioms PrimitiveReflexivity.ProjectionNecessity.lt_of_lt_succ_of_ne
#print axioms PrimitiveReflexivity.ProjectionNecessity.bounded_search
#print axioms PrimitiveReflexivity.ProjectionNecessity.pigeonhole
