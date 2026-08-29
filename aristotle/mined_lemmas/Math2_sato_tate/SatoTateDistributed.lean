import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

def SatoTateDistributed (θ : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → Tendsto (fun N => primeAvg θ f N) atTop (𝓝 (stIntegral f))

/-- The `m`-th Weyl test function `θ ↦ U_m (cos θ)`, where `U_m` is the Chebyshev polynomial
of the second kind; equivalently `θ ↦ sin ((m+1)θ) / sin θ`.  This is the character of the
`m`-th symmetric power of the standard representation of `SU(2)`. -/
