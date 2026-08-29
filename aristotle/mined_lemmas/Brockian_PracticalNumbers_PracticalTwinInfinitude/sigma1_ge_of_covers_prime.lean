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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

lemma sigma1_ge_of_covers_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : 0 < n)
    (hple : p ≤ sigma1 n + 1) (j : ℕ) :
    Covers n → Covers (n * p ^ j) ∧ p ^ (j + 1) ≤ sigma1 (n * p ^ j) + 1 := by
  intro hcovn
  induction j with
  | zero => simpa using ⟨hcovn, hple⟩
  | succ j ih =>
    obtain ⟨hcov, hbd⟩ := ih
    refine ⟨covers_mul_prime_pow_succ hp hpn hn hcov hcovn hbd, ?_⟩
    rw [sigma1_mul_prime_pow_succ hp hpn]
    have h1 : p - 1 ≤ sigma1 n := by omega
    have h2 : p ^ (j + 1) * (p - 1) ≤ p ^ (j + 1) * sigma1 n := Nat.mul_le_mul_left _ h1
    have h3 : p ^ (j + 1) * (p - 1) = p ^ (j + 1) * p - p ^ (j + 1) := by
      rw [Nat.mul_sub, mul_one]
    have h5 : p ^ (j + 1 + 1) = p ^ (j + 1) * p := by ring
    rw [h5]
    omega

