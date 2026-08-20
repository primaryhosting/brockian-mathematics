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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to appear before any other syntax,
so the mandated header block is placed immediately after the single `import Mathlib` line.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd d (n / d) = 1`. -/

theorem usigma_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n)) (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    have hab : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hdvd
    set a := Nat.gcd d m with ha
    set b := Nat.gcd d n with hb
    have ham : a ∣ m := Nat.gcd_dvd_right d m
    have hbn : b ∣ n := Nat.gcd_dvd_right d n
    have hdiv : (m * n) / d = (m / a) * (n / b) := by
      rw [← hab, Nat.div_mul_div_comm ham hbn]
    rw [hdiv, ← hab] at hcop
    have h1 : Nat.Coprime a (m / a) :=
      (hcop.coprime_dvd_left ⟨b, rfl⟩).coprime_dvd_right ⟨n / b, rfl⟩
    have h2 : Nat.Coprime b (n / b) :=
      (hcop.coprime_dvd_left ⟨a, mul_comm a b⟩).coprime_dvd_right ⟨m / a, mul_comm _ _⟩
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨ham, hm, h1⟩, ⟨hbn, hn, h2⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, ha⟩, ⟨hbn, -, hb⟩⟩ := hab
    rw [mem_unitaryDivisors]
    refine ⟨mul_dvd_mul ham hbn, mul_ne_zero hm hn, ?_⟩
    rw [← Nat.div_mul_div_comm ham hbn]
    have hamn : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ham).coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
    have hbmn : Nat.Coprime b (m / a) :=
      (h.symm.coprime_dvd_left hbn).coprime_dvd_right (Nat.div_dvd_of_dvd ham)
    exact Nat.Coprime.mul_left (ha.mul_right hamn) (hbmn.mul_right hb)
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, ha⟩, ⟨hbn, -, hb⟩⟩ := hab
    have h1 : Nat.gcd (a * b) m = a := by
      rw [mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd (h.symm.coprime_dvd_left hbn) ham
    have h2 : Nat.gcd (a * b) n = b :=
      Nat.gcd_mul_of_coprime_of_dvd (h.coprime_dvd_left ham) hbn
    simp [h1, h2]
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1).symm

/-- The only unitary divisors of a prime power `p ^ k` are `1` and `p ^ k`. -/
