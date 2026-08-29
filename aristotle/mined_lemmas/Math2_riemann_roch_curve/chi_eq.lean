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

lemma chi_eq (D : Point →₀ ℤ) : C.chi D = C.deg D + 1 - C.genus := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [chi, C.h0_zero, C.h1_zero]
  | single_add P n E hP hn ih =>
      rw [add_comm (Finsupp.single P n) E, C.chi_add_single, C.deg_add_single, ih]; ring

end CurveData

/-- **Riemann–Roch for a smooth projective curve** (cohomological form):
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
