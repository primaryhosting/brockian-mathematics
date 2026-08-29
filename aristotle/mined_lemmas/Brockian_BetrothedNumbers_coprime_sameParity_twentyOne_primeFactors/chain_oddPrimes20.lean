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

lemma chain_oddPrimes20 :
    List.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) oddPrimes20 := by
  simp only [oddPrimes20, List.isChain_cons, List.isChain_nil, List.head?_cons,
    Option.mem_def, Option.some.injEq, forall_eq', and_true, List.head?_nil,
    IsEmpty.forall_iff, reduceCtorEq, implies_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact fun p hp hap => le_of_prime_gt_of_no_prime_between p hp hap (by decide)

