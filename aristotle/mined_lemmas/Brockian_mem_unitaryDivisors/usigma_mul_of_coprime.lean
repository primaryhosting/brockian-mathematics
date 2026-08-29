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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

lemma usigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n)) (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    have hsplit : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hdvd
    have ham : Nat.gcd d m ∣ m := Nat.gcd_dvd_right _ _
    have han : Nat.gcd d n ∣ n := Nat.gcd_dvd_right _ _
    have hdiv : m / Nat.gcd d m * (n / Nat.gcd d n) = m * n / d := by
      rw [Nat.div_mul_div_comm ham han, hsplit]
    have hd1 : m / Nat.gcd d m ∣ m * n / d := ⟨n / Nat.gcd d n, hdiv.symm⟩
    have hd2 : n / Nat.gcd d n ∣ m * n / d := ⟨m / Nat.gcd d m, by rw [← hdiv]; ring⟩
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨ham, hm, Nat.Coprime.coprime_dvd_right hd1
        (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop)⟩,
      ⟨han, hn, Nat.Coprime.coprime_dvd_right hd2
        (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop)⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, hacop⟩, ⟨hbn, -, hbcop⟩⟩ := hab
    rw [mem_unitaryDivisors]
    refine ⟨mul_dvd_mul ham hbn, hmn, ?_⟩
    have hdiv : m * n / (a * b) = m / a * (n / b) := (Nat.div_mul_div_comm ham hbn).symm
    rw [hdiv]
    have h1 : Nat.Coprime a (n / b) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
        (Nat.Coprime.coprime_dvd_left ham h)
    have h2 : Nat.Coprime b (m / a) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd ham)
        (Nat.Coprime.coprime_dvd_left hbn h.symm)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hacop h1) (Nat.Coprime.mul_right h2 hbcop)
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hd.1
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, -⟩, ⟨hbn, -, -⟩⟩ := hab
    have hbm : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hbn h.symm
    have han : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ham h
    simp [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.Coprime.gcd_mul_left_cancel b han,
      Nat.gcd_eq_left ham, Nat.gcd_eq_left hbn]
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hd.1).symm

/-- A prime power `p ^ k` (`k ≥ 1`) has exactly the two unitary divisors `1` and `p ^ k`. -/
