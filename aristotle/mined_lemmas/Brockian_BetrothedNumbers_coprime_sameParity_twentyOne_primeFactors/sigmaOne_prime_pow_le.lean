/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma sigmaOne_prime_pow_le {p k : ℕ} (hp : p.Prime) :
    (sigmaOne (p ^ k) : ℚ) ≤ (p : ℚ) ^ k * w p := by
  have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp.two_le
  have hd : (0:ℚ) < (p:ℚ) - 1 := by linarith
  have hs : (sigmaOne (p ^ k) : ℚ) = ∑ i ∈ Finset.range (k + 1), (p:ℚ) ^ i := by
    unfold sigmaOne
    rw [Nat.sum_divisors_prime_pow hp]
    push_cast
    ring_nf
  rw [hs, geom_sum_eq (by linarith)]
  have hw : (p:ℚ) ^ k * w p = ((p:ℚ) ^ (k + 1)) / ((p:ℚ) - 1) := by
    unfold w; field_simp; ring
  rw [hw]
  gcongr
  linarith

/-- The rational abundancy bound: `σ₁(N) ≤ N ∏_{p ∣ N} p/(p-1)`. -/
