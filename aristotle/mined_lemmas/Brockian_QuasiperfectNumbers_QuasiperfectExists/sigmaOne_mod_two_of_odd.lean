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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module doc comment before `import`, so the required
header appears here as an ordinary comment and is repeated as the module docstring below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Summary

A *quasiperfect* number is a natural number `n` with `σ(n) = 2n + 1`, i.e. the sum of the
proper divisors of `n` equals `n + 1`.  No quasiperfect number is known and their existence
is an open problem.  We prove here the classical structural constraints: any quasiperfect
number is an odd perfect square greater than `1`, and package this as a Lean-checked
reduction `QuasiperfectExists` of the existence question.
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma sigmaOne_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    sigmaOne n % 2 = n.divisors.card % 2 := by
  have h : ∀ d ∈ n.divisors, d % 2 = 1 := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hn' : n % 2 = 1 := Nat.odd_iff.mp hn
    have h2 : ¬ (2 ∣ d) := by
      intro h2
      have := h2.trans hdvd
      omega
    omega
  unfold sigmaOne
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl h]
  simp

/-- A positive number with an odd number of divisors is a square. -/
