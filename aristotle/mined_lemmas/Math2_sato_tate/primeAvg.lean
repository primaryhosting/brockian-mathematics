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

noncomputable def primeAvg (θ : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ p ∈ primesUpTo N, f (θ p)) / ((primesUpTo N).card : ℝ)

/-- The angles `θ p` are *Sato–Tate distributed*: the empirical measures of the angles
attached to the primes `p ≤ N` converge weakly, as `N → ∞`, to the Sato–Tate measure
`(2/π) sin²θ dθ` on `[0, π]`. -/
