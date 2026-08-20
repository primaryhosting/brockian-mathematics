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

theorem sato_tate_half (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hCM : ¬ HasCM W)
    (hST : SatoTateWeyl W) :
    Tendsto (fun N : ℕ =>
        (((goodPrimesBelow W N).filter (fun p => frobAngle W p ∈ Icc 0 (π / 2))).card : ℝ)
          / ((goodPrimesBelow W N).card : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hval : ∫ t in (0:ℝ)..(π / 2), 2 / π * Real.sin t ^ 2 = 1 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
    field_simp
    ring
  have := sato_tate W hΔ hCM hST (a := 0) (b := π / 2) le_rfl (by positivity) (by linarith)
  rwa [hval] at this

end Math2

import RequestProject.SatoTate.Chebyshev

/-!
# From the Weyl criterion to equidistribution for the Sato–Tate measure

This file contains the analytic heart of the Sato–Tate statement: if the averages of the
Chebyshev polynomials `U n` (`n ≥ 1`) evaluated at a family of angles tend to `0`, then the
angles are equidistributed with respect to the Sato–Tate measure `(2/π) sin²θ dθ`.
-/

open MeasureTheory Real Set Filter Topology
open scoped Classical

namespace Math2

/-- The average of `f ∘ θ` over the finite index set `S`. -/
