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

lemma integral_satoTateMeasure (f : ℝ → ℝ) :
    ∫ t, f t ∂satoTateMeasure = ∫ t in (0:ℝ)..π, f t * satoTateDensity t := by
  rw [satoTateMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_satoTateDensity.ennreal_ofReal)
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [smul_eq_mul, ENNReal.toReal_ofReal (satoTateDensity_nonneg t), mul_comm]

end Math2

import RequestProject.SatoTate.Measure

/-!
# Chebyshev polynomials and the Sato–Tate measure

The polynomials `U n` (Chebyshev of the second kind) form an orthonormal family for the
Sato–Tate measure; here we only need that `U n` integrates to `0` for `n ≥ 1` (and to `1`
for `n = 0`), which is the classical Weyl criterion input for Sato–Tate.
-/

open MeasureTheory Real Set Polynomial

namespace Math2

/-- `t ↦ P.eval (cos t)` is continuous. -/
