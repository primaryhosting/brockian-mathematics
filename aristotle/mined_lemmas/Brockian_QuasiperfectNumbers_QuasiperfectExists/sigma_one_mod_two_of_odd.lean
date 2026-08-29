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
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option autoImplicit false

namespace Brockian.QuasiperfectNumbers

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of its divisors
equals `2 * n + 1` (equivalently, the sum of its proper divisors is `n + 1`).
No quasiperfect number is known, and their existence is an open problem. -/

theorem sigma_one_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    (σ 1 n) % 2 = n.divisors.card % 2 := by
  rw [sigma_one_apply]
  have hdvd_odd : ∀ d ∈ n.divisors, Odd d := by
    intro d hd
    exact hn.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  have hcast : ((∑ d ∈ n.divisors, d : ℕ) : ZMod 2) = (n.divisors.card : ZMod 2) := by
    push_cast
    rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    obtain ⟨k, hk⟩ := hdvd_odd d hd
    subst hk; push_cast; ring_nf; simp [show (2 : ZMod 2) = 0 by decide]
  simpa using (ZMod.natCast_eq_natCast_iff' _ _ 2).1 hcast

/-- An odd number whose sum of divisors is odd is a square. -/
