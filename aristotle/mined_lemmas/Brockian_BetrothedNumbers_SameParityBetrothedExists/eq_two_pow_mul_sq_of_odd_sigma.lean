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

theorem eq_two_pow_mul_sq_of_odd_sigma {n : ℕ} (hn : 0 < n) (h : Odd (sigma 1 n)) :
    ∃ a b : ℕ, 0 < b ∧ n = 2 ^ a * b ^ 2 := by
  set a := n.factorization 2
  set m := ordCompl[2] n
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two (by omega))
  have hmul : sigma 1 n = sigma 1 (2 ^ a) * sigma 1 m := by
    rw [← hsplit]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hmul] at h
  have hs2 : Odd (sigma 1 m) := (Nat.odd_mul.mp h).2
  have hmpos : 0 < m := Nat.ordCompl_pos 2 (by omega)
  have hmodd : m % 2 = 1 := by
    have := Nat.not_dvd_ordCompl Nat.prime_two (n := n) (by omega)
    omega
  obtain ⟨c, hc⟩ := isSquare_of_odd_of_odd_sigma m hmpos hmodd hs2
  refine ⟨a, c, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · simp at hc; omega
    · exact hcpos
  · rw [← hsplit, hc]; ring

/-- In a same-parity betrothed pair, the common value `σ m = σ n = m + n + 1` is odd. -/
