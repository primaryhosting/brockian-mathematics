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

lemma ratio_antitone {a m : ℕ} (ha : 2 ≤ a) (ham : a ≤ m) :
    (m : ℚ) / (m - 1) ≤ (a : ℚ) / (a - 1) := by
  have ha' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have ham' : (a : ℚ) ≤ (m : ℚ) := by exact_mod_cast ham
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Comparison of `∏_{p ∈ S} p/(p-1)` against a list `L` of increasing integers `≥ 2`
having no primes in the gaps: if `S` consists of primes bounded below by the head of `L`
and `#S ≤ L.length`, then the product over `S` is at most the product over `L`. -/
