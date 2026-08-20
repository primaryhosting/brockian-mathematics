import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

noncomputable def partialDeriv (f : (Fin n → ℝ) → ℝ) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => f (Function.update x j s)) (x j)

/-- A trigonometric polynomial on the torus `𝕋ⁿ = ℝⁿ / ℤⁿ`, with modes in the finite set `K`
and Fourier coefficients `a`, `b`. -/
