import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose sum of
divisors equals their sum plus one. -/

lemma sigma_one_prime_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((σ 1 (p ^ a) : ℕ) : ℚ) ≤ (p : ℚ) ^ a * ((p : ℚ) / (p - 1)) := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  have hgeom : (∑ k ∈ Finset.range (a + 1), (p : ℚ) ^ k) * ((p : ℚ) - 1)
      = (p : ℚ) ^ (a + 1) - 1 := by
    have := geom_sum_mul (x := (p : ℚ)) (n := a + 1)
    linarith [this]
  rw [mul_div_assoc']
  rw [le_div_iff₀ (by linarith), hgeom]
  have hpow : (p : ℚ) ^ a * p = (p : ℚ) ^ (a + 1) := by ring
  linarith [hpow]

/-- The abundancy `σ₁(N)/N` is bounded by `∏_{p ∣ N} p/(p-1)` (in multiplied-out form). -/
