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

lemma ord_some_div (a : k) {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ord (some a)
        (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q)
      = (p.rootMultiplicity a : ℤ) - (q.rootMultiplicity a : ℤ) := by
  set f : RatFunc k := algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q with hf
  have hq' : algebraMap k[X] (RatFunc k) q ≠ 0 := by
    simpa [algebraMap_ne_zero_iff] using hq
  have hd' : algebraMap k[X] (RatFunc k) f.denom ≠ 0 := by
    simpa [algebraMap_ne_zero_iff] using f.denom_ne_zero
  have hcross : algebraMap k[X] (RatFunc k) p * algebraMap k[X] (RatFunc k) f.denom
      = algebraMap k[X] (RatFunc k) f.num * algebraMap k[X] (RatFunc k) q := by
    have h1 : algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom = f :=
      f.num_div_denom
    rw [← h1] at hf
    field_simp at hf
    linear_combination hf
  have hcross' : p * f.denom = f.num * q := by
    apply RatFunc.algebraMap_injective k
    push_cast [map_mul] at hcross ⊢
    exact hcross
  have hnum : f.num ≠ 0 := by
    intro h
    rw [h] at hcross'
    simp only [zero_mul] at hcross'
    exact hp (by simpa [hq] using mul_eq_zero.1 hcross' |>.resolve_right f.denom_ne_zero)
  have h1 : (p * f.denom).rootMultiplicity a = (f.num * q).rootMultiplicity a := by
    rw [hcross']
  rw [Polynomial.rootMultiplicity_mul (by simp [hp, f.denom_ne_zero]),
    Polynomial.rootMultiplicity_mul (by simp [hnum, hq])] at h1
  simp only [ord_some]
  omega

/-- Order at the place at infinity, computed from an arbitrary representation as a quotient. -/
