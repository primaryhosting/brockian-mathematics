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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers each of
whose sum of divisors equals the sum of the two numbers plus one. -/

theorem isSquare_of_odd_betrothed {m n : ℕ} (h : Betrothed m n) (hm : m % 2 = 1)
    (hn : n % 2 = 1) : IsSquare m ∧ IsSquare n := by
  have hpar : m % 2 = n % 2 := by omega
  obtain ⟨hm2, hn2⟩ := odd_sigma_of_sameParity h hpar
  have key : ∀ k : ℕ, k % 2 = 1 → (∃ a b : ℕ, 0 < b ∧ k = 2 ^ a * b ^ 2) → IsSquare k := by
    rintro k hk ⟨a, b, -, rfl⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨b, by ring⟩
    · exfalso
      have : (2 : ℕ) ∣ 2 ^ a * b ^ 2 := Dvd.dvd.mul_right (dvd_pow_self 2 ha.ne') _
      omega
  exact ⟨key m hm (eq_two_pow_mul_sq_of_odd_sigma h.1 hm2),
    key n hn (eq_two_pow_mul_sq_of_odd_sigma h.2.1 hn2)⟩

/-- **Same Parity Betrothed Exists (conditional reduction).**

Whether a betrothed (quasi-amicable) pair of the same parity exists is an open problem: all
known betrothed pairs consist of one even and one odd number.  What is proved here is the
equivalence of that open existence statement with the a priori much more restrictive
statement that a same-parity betrothed pair exists both of whose members have the shape
`2 ^ a * b ^ 2`.  In particular, if both members are odd they must both be perfect squares. -/
