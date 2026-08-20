/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/

lemma resMap_surjective (p : P) (n : ℤ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] F) (hf : ∀ v, ((-n : ℤ) : Zt) ≤ C.ord p (f v))
    (hs : ∀ y : F, ((0 : ℤ) : Zt) ≤ C.ord p y → ∃ v : V, f v = C.unif p ^ (-n) * y) :
    Function.Surjective (C.resMap p n f hf) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨v, hv⟩ := hs y hy
    refine ⟨v, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    ext
    show C.unif p ^ n * f v = y
    rw [hv, ← mul_assoc, ← zpow_add₀ (C.unif_ne_zero p)]
    simp

end PreCurve

end Math2

/-
Setup for the Riemann-Roch theorem: function fields of one variable, places,
divisors and Riemann-Roch spaces.
-/
import Mathlib

namespace Math2

open Module Submodule

universe u v w

/-- The value group with infinity. -/
abbrev Zt := WithTop ℤ

/-- Basic data of a (smooth projective) algebraic curve, described through its function
field: a field extension `F / K` together with a family of places `P`, each given by a
normalized discrete valuation of `F` which is trivial on `K`. -/
structure PreCurve (K : Type u) (F : Type v) (P : Type w) [Field K] [Field F] [Algebra K F]
    where
  /-- The (additive) valuation attached to a place. -/
  ord : P → AddValuation F Zt
  /-- The degree of a place. -/
  deg : P → ℕ
  /-- Valuations are trivial on the constants. -/
  ord_algebraMap : ∀ (p : P) (c : K), c ≠ 0 → ord p (algebraMap K F c) = (0 : Zt)
  /-- Each valuation is normalized: there is a uniformizer. -/
  uniformizer : ∀ p : P, ∃ t : F, ord p t = ((1 : ℤ) : Zt)
  /-- A nonzero function has nonzero valuation at only finitely many places. -/
  ord_support : ∀ x : F, x ≠ 0 → ∃ S : Finset P, ∀ p ∉ S, ord p x = (0 : Zt)
  /-- A principal divisor has degree zero. -/
  degree_principal : ∀ (x : F), x ≠ 0 → ∀ S : Finset P, (∀ p ∉ S, ord p x = (0 : Zt)) →
    ∑ p ∈ S, (deg p : ℤ) * ((ord p x).untopD 0) = 0
  /-- The functions which are regular everywhere are the constants. -/
  constants : ∀ x : F, (∀ p : P, (0 : Zt) ≤ ord p x) → ∃ c : K, algebraMap K F c = x
  /-- The curve has at least one place. -/
  place_nonempty : Nonempty P

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- `ord` of an element, as an integer (junk value `0` at `x = 0`). -/
