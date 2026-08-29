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

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- The sum-of-divisors function `σ₁`, written directly as a sum over `Nat.divisors`. -/

theorem sigmaSum_prime_pow_lt {p c k : ℕ} (hp : p.Prime) (hc : 3 ≤ c) (hcp : c ≤ p) :
    (c - 1) * sigmaSum (p ^ k) < c * p ^ k := by
  have hsum : sigmaSum (p ^ k) = ∑ x ∈ Finset.range (k + 1), p ^ x := by
    rw [sigmaSum, Nat.sum_divisors_prime_pow hp]
  set S := ∑ x ∈ Finset.range (k + 1), p ^ x with hSdef
  have hgeom : S * p + 1 = p ^ (k + 1) + S := geom_sum_mul_self p k
  have hpk : p ^ (k + 1) = p * p ^ k := by ring
  have hP : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  rw [hsum]
  have h1 : S * p + 1 = p * p ^ k + S := by rw [hgeom, hpk]
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 1 := ⟨p - 1, by omega⟩
  set P := (e + 1) ^ k with hPdef
  simp only [Nat.add_sub_cancel]
  have hd2 : 2 ≤ d := by omega
  have hde : d ≤ e := by omega
  have h3 : S * e + 1 = P * e + P := by nlinarith [h1]
  by_contra hcon
  push_neg at hcon
  have h2 : (d + 1) * P * e ≤ d * S * e := Nat.mul_le_mul_right e (by nlinarith [hcon])
  have h4 : d * S * e + d = d * P * e + d * P := by nlinarith [h3]
  have h5 : P * d ≤ P * e := Nat.mul_le_mul_left P hde
  nlinarith [h2, h4, h5, hP, hd2]

/-- An odd positive number with at most two distinct prime factors is deficient. -/
