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

lemma covers_four_mul_seven_pow_mul {b m : ℕ} (hb : 1 ≤ b) (hm : 0 < m)
    (hle : m ≤ 8 * 7 ^ b) : Covers (4 * 7 ^ b * m) := by
  set v := m.factorization 2 with hv
  set m₄ := m / 2 ^ v with hm₄
  have hsplit2 : 2 ^ v * m₄ = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have h2 : ¬ 2 ∣ m₄ := Nat.not_dvd_ordCompl Nat.prime_two hm.ne'
  have hm₄pos : 0 < m₄ := Nat.ordCompl_pos 2 hm.ne'
  set d := m₄.factorization 7 with hd
  set m₂ := m₄ / 7 ^ d with hm₂
  have hsplit7 : 7 ^ d * m₂ = m₄ := Nat.ordProj_mul_ordCompl_eq_self m₄ 7
  have h7 : ¬ 7 ∣ m₂ := Nat.not_dvd_ordCompl (by norm_num) hm₄pos.ne'
  have hm₂pos : 0 < m₂ := Nat.ordCompl_pos 7 hm₄pos.ne'
  have hm₂le : m₂ ≤ m := le_trans (Nat.ordCompl_le m₄ 7) (Nat.ordCompl_le m 2)
  have hm₂odd : ¬ 2 ∣ m₂ := fun h => h2 (h.trans ⟨7 ^ d, by rw [← hsplit7]; ring⟩)
  have hbase : Covers (2 ^ (2 + v) * 7 ^ (b + d)) :=
    covers_two_pow_mul_seven_pow (by omega) (b + d)
  have hcop : Nat.Coprime m₂ (2 ^ (2 + v) * 7 ^ (b + d)) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.pow_right _ (((Nat.prime_two.coprime_iff_not_dvd).mpr hm₂odd).symm)
    · exact Nat.Coprime.pow_right _ ((((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr h7).symm)
  have hdvd : 4 * 7 ^ b ∣ 2 ^ (2 + v) * 7 ^ (b + d) := by
    refine mul_dvd_mul ?_ ?_
    · have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    · exact pow_dvd_pow 7 (by omega)
  have hsigd : sigma1 (4 * 7 ^ b) ≤ sigma1 (2 ^ (2 + v) * 7 ^ (b + d)) :=
    sigma1_le_of_dvd (by positivity) hdvd
  have hsig : 8 * 7 ^ b ≤ sigma1 (4 * 7 ^ b) := sigma1_four_mul_seven_pow_ge hb
  have hbound : m₂ ≤ sigma1 (2 ^ (2 + v) * 7 ^ (b + d)) + 1 := by omega
  have hres := covers_mul_coprime m₂ (2 ^ (2 + v) * 7 ^ (b + d)) hbase hm₂pos hcop hbound
  have heq : 2 ^ (2 + v) * 7 ^ (b + d) * m₂ = 4 * 7 ^ b * m := by
    rw [pow_add, pow_add, ← hsplit2, ← hsplit7]
    ring
  rwa [heq] at hres

/-! ## Modular inverse -/

