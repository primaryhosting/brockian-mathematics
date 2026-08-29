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

lemma ord_some_aDiv (q : MonicIrr k) (D : Divisor k) :
    ord (some q) (aDiv D) = D (some q) := by
  classical
  rw [ord_aDiv]
  have : ∀ P ∈ D.support, D P * ord (some q) (placeElt P) = if P = some q then D P else 0 := by
    intro P _
    rw [ord_some_placeElt]
    by_cases h : P = some q <;> simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' D.support (some q) (fun P => D P)]
  by_cases h : (some q : Place k) ∈ D.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h]

