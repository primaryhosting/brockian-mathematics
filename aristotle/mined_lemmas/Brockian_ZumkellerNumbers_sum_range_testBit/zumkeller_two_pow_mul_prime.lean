import Mathlib

namespace Brockian.ZumkellerNumbers


theorem zumkeller_two_pow_mul_prime (k : ℕ) (p : ℕ) (hk : 1 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (hlt : p < 2 ^ (k + 1)) : Zumkeller (2 ^ k * p) := by
  obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := by
    rw [Nat.odd_iff] at hodd; exact ⟨(p + 1) / 2, by omega⟩
  have hp1 : 1 < p := hp.one_lt
  have hm1 : 1 ≤ m := by omega
  set A : ℕ := ∑ i ∈ Finset.range (k + 1), 2 ^ i with hAdef
  have hA : A + 1 = 2 ^ (k + 1) := sum_range_two_pow_succ k
  have hA1 : 1 ≤ A := by
    have : 2 ^ (k + 1) ≥ 2 := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set T : ℕ := A * m with hTdef
  set a : ℕ := T / p with hadef
  set b : ℕ := T % p with hbdef
  have hab : p * a + b = T := Nat.div_add_mod T p
  have hbp : b < p := Nat.mod_lt _ (by omega)
  have hblt : b < 2 ^ (k + 1) := lt_trans hbp hlt
  have halt : a < 2 ^ (k + 1) := by
    rw [hadef, Nat.div_lt_iff_lt_mul (by omega), ← hA]
    have h2 : 2 * (A * m) < 2 * ((A + 1) * p) := by
      have hAm : A * (2 * m) = A * (p + 1) := by rw [hm]
      nlinarith [hA1, hp1]
    have : A * m < (A + 1) * p := by omega
    simpa [hTdef] using this
  -- the two families of divisors
  set F1 : Finset ℕ := (Finset.range (k + 1)).filter (fun i => a.testBit i) with hF1
  set F2 : Finset ℕ := (Finset.range (k + 1)).filter (fun i => b.testBit i) with hF2
  have hsum1 : ∑ i ∈ F1, 2 ^ i = a := by
    rw [hF1, Finset.sum_filter]
    exact sum_range_testBit (k + 1) a halt
  have hsum2 : ∑ i ∈ F2, 2 ^ i = b := by
    rw [hF2, Finset.sum_filter]
    exact sum_range_testBit (k + 1) b hblt
  have hinj1 : Set.InjOn (fun i => 2 ^ i * p) (F1 : Set ℕ) := by
    intro x _ y _ h
    simp only at h
    have h2 : (2:ℕ) ^ x = 2 ^ y := Nat.eq_of_mul_eq_mul_right (by omega) h
    exact Nat.pow_right_injective (le_refl 2) h2
  have hinj2 : Set.InjOn (fun i => (2:ℕ) ^ i) (F2 : Set ℕ) := by
    intro x _ y _ h
    exact Nat.pow_right_injective (le_refl 2) h
  set S1 : Finset ℕ := F1.image (fun i => 2 ^ i * p) with hS1
  set S2 : Finset ℕ := F2.image (fun i => 2 ^ i) with hS2
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [hS1, Finset.mem_image] at hx1
    rw [hS2, Finset.mem_image] at hx2
    obtain ⟨i, _, hi⟩ := hx1
    obtain ⟨j, _, hj⟩ := hx2
    have heq : 2 ^ i * p = 2 ^ j := by rw [hi, hj]
    have hdvd : p ∣ 2 ^ j := Dvd.intro_left _ heq
    have : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    rw [Nat.odd_iff] at hodd
    omega
  refine ⟨S1 ∪ S2, ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_divisors]
    have hn : 2 ^ k * p ≠ 0 := by positivity
    refine ⟨?_, hn⟩
    rcases Finset.mem_union.mp hx with h | h
    · rw [hS1, Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [hF1, Finset.mem_filter, Finset.mem_range] at hi
      exact Nat.mul_dvd_mul (pow_dvd_pow 2 (by omega)) dvd_rfl
    · rw [hS2, Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [hF2, Finset.mem_filter, Finset.mem_range] at hi
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) p
  · rw [Finset.sum_union hdisj, hS1, hS2, Finset.sum_image hinj1, Finset.sum_image hinj2,
      ← Finset.sum_mul, hsum1, hsum2, sum_divisors_two_pow_mul_prime k p hp hodd, ← hAdef]
    have hfin : a * p + b = A * m := by rw [mul_comm a p, hab, hTdef]
    calc 2 * (a * p + b) = 2 * (A * m) := by rw [hfin]
      _ = A * (2 * m) := by ring
      _ = A * (p + 1) := by rw [hm]

end Brockian.ZumkellerNumbers

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

