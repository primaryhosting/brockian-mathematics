/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module doc-comment `/-! ... -/` before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial UniqueFactorizationMonoid

namespace Math2

/-!
## The Riemann–Roch theorem, cohomological form

`CurveData Point` bundles the standard cohomological data of a smooth projective curve
whose closed points are indexed by `Point`:

* `ptDeg P` is the degree of the closed point `P`;
* `h0 D` and `h1 D` are `dim H⁰(X, 𝒪(D))` and `dim H¹(X, 𝒪(D))`;
* `canonical` is a canonical divisor `K` and `genus` is the genus `g = dim H¹(X, 𝒪)`;
* `chi_step` is additivity of the Euler characteristic along the exact sequence
  `0 → 𝒪(D) → 𝒪(D+P) → k(P) → 0`;
* `serre_duality` is Serre duality `H¹(D)^∨ ≅ H⁰(K - D)`.
-/

/-- Cohomological data of divisors on a smooth projective curve. -/
structure CurveData (Point : Type*) where
  /-- The degree of a closed point. -/
  ptDeg : Point → ℤ
  /-- `h0 D = dim H⁰(X, 𝒪(D)) = ℓ(D)`. -/
  h0 : (Point →₀ ℤ) → ℤ
  /-- `h1 D = dim H¹(X, 𝒪(D))`. -/
  h1 : (Point →₀ ℤ) → ℤ
  /-- A canonical divisor of the curve. -/
  canonical : Point →₀ ℤ
  /-- The genus of the curve. -/
  genus : ℤ
  /-- `ℓ(0) = 1`: the global regular functions are the constants. -/
  h0_zero : h0 0 = 1
  /-- `dim H¹(X, 𝒪) = g`. -/
  h1_zero : h1 0 = genus
  /-- Additivity of the Euler characteristic along `0 → 𝒪(D) → 𝒪(D+P) → k(P) → 0`. -/
  chi_step : ∀ (D : Point →₀ ℤ) (P : Point),
    h0 (D + Finsupp.single P 1) - h1 (D + Finsupp.single P 1) = (h0 D - h1 D) + ptDeg P
  /-- Serre duality. -/
  serre_duality : ∀ D, h1 D = h0 (canonical - D)

namespace CurveData

variable {Point : Type*} (C : CurveData Point)

/-- The degree of a divisor. -/

theorem CurveData.deg_canonical {Point : Type*} (C : CurveData Point) :
    C.deg C.canonical = 2 * C.genus - 2 := by
  have h := riemann_roch_curve C C.canonical
  rw [sub_self, C.h0_zero] at h
  have hK : C.h0 C.canonical = C.genus := by
    have := C.serre_duality 0
    rw [C.h1_zero, sub_zero] at this
    exact this.symm
  rw [hK] at h
  omega

end Math2

import RequestProject.RiemannRochCurve

/-!
# The projective line and its Riemann–Roch theorem

We realise the smooth projective curve `ℙ¹` over an arbitrary field `k` through its function
field `k(t) = RatFunc k`.  Its closed points are the monic irreducible polynomials
(the finite points) together with the point at infinity.  We define the order of vanishing
`ord P f` of a rational function at a place, the Riemann–Roch space
`L(D) = {f | f = 0 ∨ ∀ P, ord P f ≥ -D P}`, and prove `ℓ(D) = max (deg D + 1) 0`.
-/

open Polynomial
open scoped Classical

namespace Math2
namespace P1

variable (k : Type*) [Field k]

/-- Monic irreducible polynomials: the finite closed points of `ℙ¹`. -/
abbrev MonicIrr := {p : k[X] // p.Monic ∧ Irreducible p}

/-- Closed points of `ℙ¹` over `k`: a monic irreducible polynomial, or the point at
infinity (`none`). -/
abbrev Place := Option (MonicIrr k)

/-- Divisors on `ℙ¹`. -/
abbrev Divisor := Place k →₀ ℤ

variable {k}

