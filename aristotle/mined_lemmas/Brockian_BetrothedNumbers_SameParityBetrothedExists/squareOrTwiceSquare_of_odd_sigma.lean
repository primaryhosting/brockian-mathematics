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

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each one's
sum of divisors equals `m + n + 1`. -/

lemma squareOrTwiceSquare_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (h : Odd (σ 1 n)) :
    SquareOrTwiceSquare n := by
  obtain ⟨k, m, hmodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hmodd)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop] at h
  have hsm : Odd (σ 1 m) := h.of_dvd_nat (Dvd.intro_left _ rfl)
  obtain ⟨a, ha⟩ := isSquare_of_odd_sigma_of_odd hmodd hsm
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨2 ^ j * a, Or.inl (by subst hj ha; ring)⟩
  · exact ⟨2 ^ j * a, Or.inr (by subst hj ha; ring)⟩

/-- A member of a betrothed pair is nonzero. -/
