# Reproducing the R3 (A-Metric Independence) Lean Testing Session

This covers the live Lean checks done for Axiom R3 of "Foundations of Primitive
Reflexivity": the tautological version, the decorated (assumed-hypothesis) version,
and the three derived versions (metric, order, algebraic). None of this needs
Mathlib — every file here type-checks against bare Lean 4 alone, which is why setup
is much lighter than the full `Foundations.lean` project.

---

## 1. Setup — bare Lean 4, no Mathlib

Mathlib wasn't needed for any of this, so skip `lake`/`elan`'s usual toolchain
resolution (which failed in this session — `release.lean-lang.org` wasn't reachable)
and pull the Lean release directly from GitHub instead.

```sh
# 1. Install zstd if you don't have it (the release archive is .tar.zst)
apt-get update && apt-get install -y zstd     # Debian/Ubuntu
# or: brew install zstd                        # macOS

# 2. Download the Lean 4.33.1 release directly from GitHub releases
#    (matches the Mathlib rev — 0df444a3 — used in the main Foundations.lean project;
#    bump the version tag if you're targeting a different pin)
curl -sL -o lean.tar.zst \
  "https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst"

# 3. Extract
mkdir -p lean-4.33.1
tar --use-compress-program=unzstd -xf lean.tar.zst -C lean-4.33.1 --strip-components=1

# 4. Confirm the binary works
./lean-4.33.1/bin/lean --version
```

(For macOS, use the `lean-4.33.1-darwin.tar.zst` asset from the same release page;
for Windows, `lean-4.33.1-windows.zip`.)

## 2. Check any file

```sh
./lean-4.33.1/bin/lean <file>.lean
```

A clean run prints only what your `#check`/`#print axioms` commands ask for, with no
`error:` lines. Warnings (like unused-variable linter notices) are not failures —
they were actually useful signal in this session (see §3.2 and §3.5 below).

---

## 3. The five scripts, in the order they were built

### 3.1 `R3_tautological.lean` — R3 taken maximally literally

Compiles by `rfl` alone; the linter flags `extra` as unused, which is the whole
point — the statement never gave the added structure anywhere to matter.

```lean
variable {N : Type}

theorem a_metric_independence
    (R : N → N → Prop) (M : Type) (extra : N → N → M) :
    ∀ x : N, R x x ↔ R x x := by
  intro x
  rfl

#print axioms a_metric_independence
#check @a_metric_independence
```

**Expected output:** a warning that `extra` is unused, then
`'a_metric_independence' does not depend on any axioms`.

### 3.2 `R3_decorated.lean` — extra genuinely appears, but via an assumed hypothesis

```lean
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
```

**Expected output:** no warnings, `does not depend on any axioms`. Note: an earlier
draft of this also took `(hR : ∀ x, R x x)` as a hypothesis — Lean flagged it as
unused, and it was removed. That's worth reproducing as a step, not skipping to the
clean version, if you want to see the same signal.

### 3.3 `R3_metric.lean` — the diagonal fact derived from real metric axioms

```lean
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
```

**Expected output:** no warnings, `does not depend on any axioms`. Only `dist_self`
is used in the proof — `dist_symm` and `dist_triangle` are part of a genuine metric
but not needed for this result (worth noting honestly rather than pretending the
full metric structure was required).

### 3.4 `R3_algebraic.lean` — the algebraic-identity analog

```lean
namespace PrimitiveReflexivity

class BareMonoid (M : Type) where
  op : M → M → M
  zero : M
  op_zero (x : M) : op x zero = x

def AlgebraicDecorated {N M : Type} [BareMonoid M]
    (R : N → N → Prop) (extra : N → M) (x y : N) : Prop :=
  R x y ∧ (BareMonoid.op (extra x) BareMonoid.zero = extra x)

theorem a_metric_independence_algebraic
    {N M : Type}
    [m : BareMonoid M]
    (R : N → N → Prop)
    (extra : N → M)
    (x : N) :
    AlgebraicDecorated R extra x x ↔ R x x := by
  constructor
  · rintro ⟨hR, _⟩
    exact hR
  · intro hR
    constructor
    · exact hR
    · exact BareMonoid.op_zero (extra x)

#print axioms a_metric_independence_algebraic
#check @a_metric_independence_algebraic

end PrimitiveReflexivity
```

**Expected output:** no warnings, `does not depend on any axioms`. Note `BareMonoid`
is not actually a monoid as usually defined — no associativity, no left-identity
axiom (`op zero x = x`) — only the single right-identity axiom `op x zero = x` is
assumed, and that's also all the proof uses.

### 3.5 `R3_order.lean` — the order analog, completing the third leg

```lean
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
```

**Expected output:** no warnings, `does not depend on any axioms`. `le_trans` and
`le_antisymm` are included as genuine partial-order axioms but go unused — only
`le_refl` is needed.

---

## 4. What the full set actually establishes (and doesn't)

Across §3.3–3.5, each "external structure" contributes exactly one axiom to the
proof — a reflexivity-shaped fact baked into the definition of that kind of
structure (`dist_self`, `le_refl`, `op_zero`) — and none of the richer structure
(triangle inequality, transitivity/antisymmetry, associativity/left-identity) is
load-bearing. The honest summary: diagonal invariance under a decoration isn't
really a fact about metrics, orders, or algebra specifically — it's a fact about
any structure that happens to carry a reflexivity-shaped axiom, composing trivially
with another reflexive relation on the diagonal. That's real and now fully checked
in all three cases, not asserted for one of them. It is *not* a demonstration that
`0`, `True`, or an identity element are anything other than ordinary fixed values
in a static, already-elaborated proof term — the "process" framing describes the
order in which a tactic script is written, not anything about the mathematical
objects `rw`/`exact` operate on.
