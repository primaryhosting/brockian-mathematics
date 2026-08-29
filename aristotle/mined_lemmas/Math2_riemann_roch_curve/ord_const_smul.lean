import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Riemann–Roch for the smooth projective curve `ℙ¹`

We develop, from scratch, the divisor theory of the smooth projective curve `ℙ¹` over an
algebraically closed field `k`, whose function field is `RatFunc k`.

* The closed points (places) of `ℙ¹` are the elements of `k` together with the point at
  infinity; this is modelled by `Math2.Place k := Option k` (`none` is the point at infinity).
  Algebraic closedness of `k` is what makes this list of places complete.
* For every place `P` we have the normalized order (valuation) function `Math2.ord P`.
* Divisors are finitely supported `ℤ`-valued functions on places, of degree the sum of their
  coefficients (every closed point of `ℙ¹` over an algebraically closed field has degree one).
* `Math2.LSpace D` is the Riemann–Roch space `L(D) = {f | div f + D ≥ 0} ∪ {0}` and
  `Math2.ell D = ℓ(D)` is its dimension over `k`.
* `Math2.canonical k = -2 ⬝ ∞` is the canonical divisor (the divisor of the differential `dX`)
  and the genus is `g = ℓ(K)`.

The main theorem `Math2.riemann_roch_curve` is `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.
-/

namespace Math2

open Polynomial RatFunc

variable {k : Type*} [Field k]

/-- The closed points of `ℙ¹` over an algebraically closed field `k`: the elements of `k`,
together with the point at infinity `none`. -/
abbrev Place (k : Type*) : Type _ := Option k

/-- The normalized valuation of a rational function at a place of `ℙ¹`:
at a point `a ∈ k` it is the order of vanishing at `a`, at `∞` it is minus the degree. -/

lemma ord_const_smul (c : k) (hc : c ≠ 0) (f : RatFunc k) (P : Place k) :
    ord P (c • f) = ord P f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hcm : (c • f) = algebraMap k[X] (RatFunc k) (Polynomial.C c) * f := by
      rw [Algebra.smul_def]
      congr 1
      simp [RatFunc.algebraMap_eq_C]
    have hCne : (Polynomial.C c : k[X]) ≠ 0 := by simpa using hc
    have hne : algebraMap k[X] (RatFunc k) (Polynomial.C c) ≠ 0 := by
      simpa [algebraMap_ne_zero_iff] using hCne
    rw [hcm, ord_mul hne hf]
    cases P with
    | none => rw [ord_algebraMap_none hCne]; simp
    | some a =>
        rw [ord_algebraMap_some a hCne, Polynomial.rootMultiplicity_eq_zero (by
          simp [Polynomial.IsRoot, hc])]
        simp

/-! ### Divisors -/

/-- A divisor on `ℙ¹`: a finitely supported `ℤ`-valued function on the places. -/
abbrev Divisor (k : Type*) [Field k] : Type _ := Place k →₀ ℤ

/-- The degree of a divisor (every closed point has degree one). -/
