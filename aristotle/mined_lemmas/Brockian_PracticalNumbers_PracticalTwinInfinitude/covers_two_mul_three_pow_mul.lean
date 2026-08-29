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

lemma covers_two_mul_three_pow_mul {a m : ℕ} (ha : 1 ≤ a) (hm : 0 < m) (hodd : ¬ 2 ∣ m)
    (hle : m ≤ 4 * 3 ^ a) : Covers (2 * 3 ^ a * m) := by
  set c := m.factorization 3 with hc
  set m₃ := m / 3 ^ c with hm₃
  have hsplit : 3 ^ c * m₃ = m := Nat.ordProj_mul_ordCompl_eq_self m 3
  have h3 : ¬ 3 ∣ m₃ := Nat.not_dvd_ordCompl Nat.prime_three hm.ne'
  have hm₃le : m₃ ≤ m := Nat.ordCompl_le m 3
  have hm₃pos : 0 < m₃ := Nat.ordCompl_pos 3 hm.ne'
  have hm₃odd : ¬ 2 ∣ m₃ := fun h => hodd (h.trans ⟨3 ^ c, by rw [← hsplit]; ring⟩)
  have hbase : Covers (2 * 3 ^ (a + c)) := covers_two_mul_three_pow (a + c)
  have hcop : Nat.Coprime m₃ (2 * 3 ^ (a + c)) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact ((Nat.prime_two.coprime_iff_not_dvd).mpr hm₃odd).symm
    · exact Nat.Coprime.pow_right _ (((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm)
  have hsig : 4 * 3 ^ (a + c) ≤ sigma1 (2 * 3 ^ (a + c)) :=
    sigma1_two_mul_three_pow_ge (by omega)
  have hmono : (3 : ℕ) ^ a ≤ 3 ^ (a + c) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbound : m₃ ≤ sigma1 (2 * 3 ^ (a + c)) + 1 := by omega
  have := covers_mul_coprime m₃ (2 * 3 ^ (a + c)) hbase hm₃pos hcop hbound
  have heq : 2 * 3 ^ (a + c) * m₃ = 2 * 3 ^ a * m := by
    rw [pow_add]
    rw [← hsplit]
    ring
  rwa [heq] at this

