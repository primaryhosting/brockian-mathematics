import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
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

namespace Brockian.BetrothedNumbers.Dynamics

/-- The divisor-sum function `σ = σ₁`, `σ m = ∑ d ∣ m, d`. -/

def sigmaOne (m : ℕ) : ℕ := ArithmeticFunction.sigma 1 m

theorem thabit_balance_identity {k p m : ℕ}
    (hm : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : sigmaOne m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    sigmaOne m + 2 ^ (k + 1) = 2 * m + (p + 3)
      ∧ (sigmaOne m < 2 * m ↔ p + 3 < 2 ^ (k + 1))
      ∧ (sigmaOne m = 2 * m ↔ p + 3 = 2 ^ (k + 1))
      ∧ (2 * m < sigmaOne m ↔ 2 ^ (k + 1) < p + 3) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [hpow] at hsigma ⊢
  set x : ℕ := 2 ^ k with hx
  set S : ℕ := sigmaOne m with hS
  clear_value x S
  have key : S + 2 * x = 2 * m + (p + 3) := by nlinarith
  refine ⟨key, ?_, ?_, ?_⟩ <;> omega

/-- The hypotheses of `thabit_balance_identity` are satisfiable nontrivially:
`k = 4`, `p = 3`, `m = (2 ^ 4 - 1) * 5 = 75`, with `σ 75 = 124 = (2 ^ 5 - 1) * 4`. -/
