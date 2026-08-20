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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma odd_superperfect_structure {n : ℕ} (hn : Odd n) (hs : Superperfect n) :
    ∃ a k, Odd k ∧ sig n = 2 ^ a * k ∧ (2 ^ (a + 1) - 1) * sig k = 2 * n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨a, k, hk, hm⟩ := Nat.exists_eq_two_pow_mul_odd (sig_ne_zero hn0)
  refine ⟨a, k, hk, hm, ?_⟩
  have hcop : Nat.gcd (2 ^ a) k = 1 :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hk)
  have h2 := hs
  rw [Superperfect, hm, show sig (2 ^ a * k) = sig (2 ^ a) * sig k from
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_sigma hcop, sig_two_pow] at h2
  exact h2

/-- No odd prime is superperfect. -/
