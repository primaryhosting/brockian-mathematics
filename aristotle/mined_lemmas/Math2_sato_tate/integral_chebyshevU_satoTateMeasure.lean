import Mathlib
import RequestProject.SatoTate.Equidistribution

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above is placed directly after the `import` lines, since Lean 4 requires
`import` commands to come first in a file.)

## Contents

We formalise the Sato–Tate distribution of Frobenius angles of an elliptic curve over `ℚ`,
given by an integral Weierstrass model `W`.

* `Math2.frobAngle W p` is the Frobenius angle `θ_p ∈ [0, π]` at a prime `p`, defined by
  `a_p = 2 √p cos θ_p` where `a_p = p + 1 - #E(𝔽_p)` is the trace of Frobenius.
* `Math2.satoTateDensity` is the Sato–Tate density `(2/π) sin²θ` and `Math2.satoTateMeasure`
  is the associated probability measure on `[0, π]`.
* `Math2.SatoTateWeyl W` is the Weyl-criterion form of the Sato–Tate law: the averages over
  primes of good reduction of `U n (cos θ_p)` tend to `0` for every `n ≥ 1`, where `U n` is
  the `n`-th Chebyshev polynomial of the second kind (the character of the `n`-th symmetric
  power of the standard representation of `SU(2)`).  This is exactly the statement supplied
  by the potential automorphy theorems for a non-CM elliptic curve over `ℚ`.
* `Math2.sato_tate` deduces from it the distributional form of the Sato–Tate law: the
  proportion of primes `p ≤ N` of good reduction whose Frobenius angle lies in `[a, b]`
  converges to `(2/π) ∫_a^b sin²t dt`.
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

namespace Math2

open Filter Topology MeasureTheory Set

/-- The number of points of the reduction of the integral Weierstrass model `W` modulo `p`
(including the point at infinity). -/

lemma integral_chebyshevU_satoTateMeasure (n : ℕ) (hn : 1 ≤ n) :
    ∫ t, (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t) ∂satoTateMeasure = 0 := by
  rw [integral_satoTateMeasure]
  have key : ∀ t : ℝ, (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (Real.cos t) * satoTateDensity t
      = 1 / π * Real.cos (n * t) - 1 / π * Real.cos ((n + 2 : ℕ) * t) := by
    intro t
    have h := Polynomial.Chebyshev.U_real_cos t (n:ℤ)
    have hcc : Real.cos ((n:ℝ) * t) - Real.cos (((n:ℝ) + 2) * t)
        = 2 * Real.sin (((n:ℝ) + 1) * t) * Real.sin t := by
      rw [Real.cos_sub_cos]
      have h1 : ((n:ℝ) * t + ((n:ℝ) + 2) * t) / 2 = ((n:ℝ) + 1) * t := by ring
      have h2 : ((n:ℝ) * t - ((n:ℝ) + 2) * t) / 2 = -t := by ring
      rw [h1, h2, Real.sin_neg]
      ring
    have hcast : ((n + 2 : ℕ) : ℝ) = (n:ℝ) + 2 := by push_cast; ring
    rw [hcast]
    unfold satoTateDensity
    have hrw : (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (Real.cos t) * (2 / π * Real.sin t ^ 2)
        = 2 / π * ((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (Real.cos t) * Real.sin t)
          * Real.sin t := by
      ring
    rw [hrw, h]
    push_cast
    linear_combination (-1 / π) * hcc
  simp only [key]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_nat_mul_zero_pi hn, integral_cos_nat_mul_zero_pi (by omega : 1 ≤ n + 2)]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Every real polynomial is a linear combination of Chebyshev polynomials of the second kind:
this is packaged as an induction principle. -/
