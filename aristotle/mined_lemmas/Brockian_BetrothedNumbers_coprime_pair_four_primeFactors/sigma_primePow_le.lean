import Mathlib
/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n` such that
the sum of the divisors of each equals `m + n + 1`, i.e. each is the sum of the *nontrivial*
divisors (excluding `1` and the number itself) of the other. -/

lemma sigma_primePow_le (p k : ℕ) (hp : p.Prime) :
    ((sigma 1 (p ^ k) : ℕ) : ℚ) ≤ (p : ℚ) ^ k * ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hpm : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  push_cast
  have hgeom : ∑ x ∈ Finset.range (k + 1), (p : ℚ) ^ x
      = ((p : ℚ) ^ (k + 1) - 1) / ((p : ℚ) - 1) := by
    rw [geom_sum_eq]; linarith
  have hr : (p : ℚ) ^ k * ((p : ℚ) / ((p : ℚ) - 1)) = ((p : ℚ) ^ (k + 1)) / ((p : ℚ) - 1) := by
    field_simp; ring
  rw [hgeom, hr]
  gcongr
  linarith

/-- The abundancy of `N` is bounded by the Euler product `∏_{p ∣ N} p/(p-1)`. -/
