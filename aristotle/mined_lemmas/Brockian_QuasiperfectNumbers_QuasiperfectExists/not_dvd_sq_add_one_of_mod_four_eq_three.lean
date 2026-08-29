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

lemma not_dvd_sq_add_one_of_mod_four_eq_three {m v : ℕ} (hm : m % 4 = 3) :
    ¬ m ∣ v ^ 2 + 1 := by
  intro hdvd
  have hm0 : m ≠ 0 := by omega
  haveI : NeZero m := ⟨hm0⟩
  have hsq : IsSquare (-1 : ZMod m) := by
    refine ⟨(v : ZMod m), ?_⟩
    have h0 : ((v ^ 2 + 1 : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    linear_combination -h0
  have hall : ∀ q ∈ m.primeFactors, q % 4 = 1 := by
    intro q hq
    have h3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq hsq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    rcases hqp.eq_two_or_odd with h2 | h2
    · subst h2; omega
    · omega
  have := mod_four_eq_one_of_primeFactors hm0 hall
  omega

/-- **Every quasiperfect number is odd.**

If `n = 2 ^ k * u` with `u` odd and `k ≥ 1`, then `σ(n) = (2 ^ (k+1) - 1) * σ(u) = 2n + 1`
forces `M := 2 ^ (k+1) - 1` to divide `u + 1`, while `σ(u)` is odd, so `u = v ^ 2`.
Thus `M ≡ 3 (mod 4)` divides `v ^ 2 + 1`, which is impossible. -/
