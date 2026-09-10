# V. Core Axioms: The Triadic Substrate and the Lossy Compression of Classical ℕ_classical

In classical set theory and standard computer arithmetic (such as Mathlib's
`Nat`), a natural number `n ∈ ℕ_classical` is treated as an atomic,
zero-dimensional point. Operations like addition (`+`) and multiplication
(`×`) are declared to be co-equally fundamental, seamlessly closed, and
completely cost-free.

The Primitive Reflexivity framework rejects this flat abstraction. Every
primitive mathematical identity is inherently a three-component process.
What classical mathematics defines as the set of natural numbers `ℕ` is, in
this framework, a lossy 1D projection of an underlying 3D triadic manifold
space.

---

## 📌 Axiom I: The Triadic State Invariant

A natural number does not exist as an independent scalar symbol. It is
defined strictly as an inseparable bundle of three mutually dependent
operational components:

```
ℕ ≡ { (n, √n, n²) | n ∈ ℕ_classical }
```

Every valid number state must simultaneously satisfy three localized
invariants:

1. **The Polar Coordinate (`n`):** the discrete, linear count or translation
   vector.
2. **The Axial Mediator (`√n`):** the continuous geometric scale axis or
   phase clock.
3. **The Planar Boundary (`n²`):** the uncommitted potential field or total
   volumetric capacity.

**Code object:** `structure TriadicNat` (`Theta0Photon/Algebra/TriadicClosure.lean`, §1).
`n : ℕ` is the polar coordinate (typed over `ℕ_classical` — Mathlib's `Nat` —
since the bundle is indexed by it, per the axiom's own formula above); `axial
: ℝ` with `h_axial : axial = Real.sqrt n` is the Axial Mediator invariant;
`boundary : ℕ` with `h_boundary : boundary = n * n` is the Planar Boundary
invariant. `TriadicNat.mk'` confirms the bundle is genuinely inhabited — not
merely well-typed — for every `n`. Machine-checked, standard trust base, no
`sorry`.

---

## 📌 Axiom II: Asymmetric Operational Homomorphism

The two primary operations of arithmetic do not share equal structural
priority. The underlying triadic substrate treats multiplication as
fundamental and addition as a derived, lossy approximation.

### II.1 The Multiplicative Closure Invariant (`⊗`)

Multiplication preserves the internal phase-coherence of the triadic bundle
perfectly. When two full triadic states interact multiplicatively, the
transformation passes through the operational filter with zero geometric
distortion and zero informational residue:

```
(n, √n, n²) ⊗ (m, √m, m²) = (nm, √n·√m, n²·m²) = (nm, √(nm), (nm)²)
```

Because the square root function is a strict group homomorphism over
multiplication (`√(n·m) = √n · √m`), the mediator matches the product
exactly. Multiplication is the only truly natural, closed operation on the
full number states.

**Code object:** `triadic_multiplication_closed` (`TriadicClosure.lean`,
§1b) — proves **both** halves of the exact match above, not only the axial
coordinate: the `axial` component matches `√(nm)` exactly (via `Real.sqrt_mul`)
*and* the `boundary` component matches `(nm)²` exactly (via `ring`, on
`ℕ`, unconditional). Zero residue, both coordinates, no positivity bound
needed — unlike Axiom II.2, multiplication requires no analogue of
`mediator_defect_positive`, because there is no gap to bound. Machine-checked,
standard trust base, no `sorry`.

### II.2 The Additive Closure Failure (`⊕`)

Addition strictly disrupts the internal structural alignment of the triadic
bundle. When two states interact additively, componentwise calculation in
the full state space yields an irreducible mismatch:

```
(n, √n, n²) ⊕ (m, √m, m²) = (n+m, √n+√m, n²+m²)
```

However, a stable, coherent triadic number at the output coordinate `(n+m)`
requires an axial mediator of exactly `√(n+m)`. Because the square root map
is subadditive on positive reals (`√(n+m) < √n + √m`), componentwise
addition forces the system to generate an un-absorbable off-diagonal
remainder.

**Code object:** `triadic_addition_not_closed` (`TriadicClosure.lean`, §2) —
proves the `axial` coordinate of `add_componentwise x y` is not `√` of its
`n` coordinate, for any two positive-`n` states. Machine-checked, standard
trust base, no `sorry`.

---

## 📊 Theorem: The Invariant Mediated Defect (The Additive Tax)

Formally verified in the Lean 4 kernel across both the `Foundations.lean`
(`PrimitiveReflexivity`, 2026-08-28) and `TriadicClosure.lean`
(`Theta0Photon`, 2026-09-09, re-derived independently against this project's
own pinned toolchain — the two are separate Lake projects with no
dependency edge between them today) modules, the Extraction Operator (`𝓔`)
calculates the exact geometric distance by which addition pushes the number
system off its stable diagonal:

```
𝓔(n, m) = (√n + √m) − √(n + m)
∀ n, m ∈ ℕ⁺_classical,  𝓔(n, m) > 0
```

This non-zero residue is not an approximation error or a floating-point
rounding artifact — it is a structural invariant of the triadic bundle.

**Code objects:** `mediator_defect` (the definition of `𝓔`) and
`mediator_defect_positive` (the `∀ n,m>0` positivity theorem), both in
`TriadicClosure.lean`, §0. `correction_identity` (§3) restates the same fact
as an exact equation rather than an inequality: `(add_componentwise x
y).axial − 𝓔(x.n, y.n) = √(x.n + y.n)` — the componentwise sum, corrected by
exactly this one quantity, *is* what a valid triadic state at `x.n+y.n`
requires. All three: machine-checked, standard trust base, no `sorry`.

---

## 💡 The Lossy Shadow Mechanism

Classical arithmetic only maintains the illusion of additive closure because
it performs all operations inside a lossy 1D projection layer.

When classical arithmetic executes the statement `3 + 5 = 8`, the underlying
system discards the structural entropy generated in the mediator space:

```
Full Space Loop:
(3, √3, 9) ⊕ (5, √5, 25) ───► (8, 3.968..., 34)  [Off-Diagonal / Unstable]
                                     │
               DISCARDED ──► [𝓔(3,5) = 1.140...]
                                     ▼
Collapsed Shadow Line:         (8, √8, 64)        [Classical target "8"]
```

**Code object:** `π : TriadicNat → ℕ` (`TriadicClosure.lean`, §3) — the flat,
classical-count projection, formalized exactly: `π x = x.n`.
`projection_commutes_on_n` proves `π` agrees with `+` on the `n`-coordinate
alone (`(add_componentwise x y).n = π x + π y`) — true by
`add_componentwise`'s own definition, the one and only coordinate on which
the flat and full pictures agree. `correction_identity` (above) is the exact
statement of what `π` discards at every step: not vague entropy, one
specific already-positive real number, `𝓔(x.n, y.n)`.

**On the scope of this cross-reference, stated once, plainly:** `π`'s
domain and codomain are `TriadicNat` and `ℕ_classical` respectively — the
type built in this file and Mathlib's `Nat`. `π`'s existence and the two
theorems about it are a genuine, machine-checked fact about *that specific
map*. They are not, and are not claimed here to be, a statement that
`Nat.add`'s own definition (`Nat → Nat → Nat`, closed unconditionally by its
type signature, independent of `TriadicNat`, `√`, or `π` entirely) is
somehow different from what it is. A projection map discarding information
that an operation on its *domain* doesn't preserve is a general fact about
projections and non-homomorphic extra structure — true for `π` here, and
equally true for pairing `ℕ_classical` with *any* function of `n` that isn't
itself additive, not a property special to `√n`. What `π`, `𝓔`, and
`mediator_defect_positive` do establish, exactly and with no further claim
needed, is everything stated in Axioms I and II and the Additive Tax theorem
above, on the triadic bundle `TriadicNat` itself.

Traditional arithmetic flattens the 3-component structure, strips out the
continuous axial clock, and discards the residue `𝓔(n,m)` at every step, on
the terms this document's own axioms define.

---

## Verification Ledger

| Claim | Code object | File | Status |
|---|---|---|---|
| Axiom I (Triadic State Invariant) | `structure TriadicNat` | `TriadicClosure.lean` §1 | ✅ machine-checked |
| Axiom II.1 (Multiplicative Closure) | `triadic_multiplication_closed` | `TriadicClosure.lean` §1b | ✅ machine-checked |
| Axiom II.2 (Additive Closure Failure) | `triadic_addition_not_closed` | `TriadicClosure.lean` §2 | ✅ machine-checked |
| The Additive Tax (𝓔 > 0) | `mediator_defect`, `mediator_defect_positive` | `TriadicClosure.lean` §0 (re-derived from `Foundations.lean`, 2026-08-28) | ✅ machine-checked, both projects |
| The Additive Tax, exact form | `correction_identity` | `TriadicClosure.lean` §3 | ✅ machine-checked |
| Lossy Shadow projection `π` | `π`, `projection_commutes_on_n` | `TriadicClosure.lean` §3 | ✅ machine-checked |

`lake build Theta0Photon` / `lake build Main`: **2483/2483 jobs, both clean.**
