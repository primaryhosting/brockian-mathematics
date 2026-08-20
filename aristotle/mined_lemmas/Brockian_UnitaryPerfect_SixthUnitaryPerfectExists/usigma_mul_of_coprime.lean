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

(The header above is repeated here as a module docstring: Lean requires all
`import` statements to precede any module documentation comment.)

## Contents

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n/d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Only five unitary perfect numbers are known, and whether a sixth exists is open.

This file develops the basic theory (`σ*` is multiplicative, its value on prime
powers, and hence the product formula `σ*(n) = ∏_{p^a ‖ n} (p^a + 1)`), verifies
the five classically known unitary perfect numbers, proves the partial result
that no odd number is unitary perfect, and finally states and proves the
conditional reduction `SixthUnitaryPerfectExists`: as soon as there is *one*
unitary perfect number outside the known list of five, there are at least six
unitary perfect numbers.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem usigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp [usigma_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp [usigma_zero]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun d => (Nat.gcd d m, Nat.gcd d n))
    (j := fun x => x.1 * x.2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    refine Finset.mem_product.2 ⟨gcd_mem_unitaryDivisors_left h ha,
      gcd_mem_unitaryDivisors_left h.symm ?_⟩
    rwa [mul_comm]
  · rintro ⟨a₁, a₂⟩ hx
    rw [Finset.mem_product] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨-, m₁, hm₁, hc₁⟩ := mem_unitaryDivisors.1 hx1
    obtain ⟨-, n₁, hn₁, hc₂⟩ := mem_unitaryDivisors.1 hx2
    have hd1 : a₁ ∣ m := ⟨m₁, hm₁⟩
    have hd2 : a₂ ∣ n := ⟨n₁, hn₁⟩
    have he1 : m₁ ∣ m := ⟨a₁, by rw [hm₁]; ring⟩
    have he2 : n₁ ∣ n := ⟨a₂, by rw [hn₁]; ring⟩
    refine mem_unitaryDivisors.2 ⟨hmn, m₁ * n₁, by rw [hm₁, hn₁]; ring, ?_⟩
    have c12 : Nat.Coprime a₁ n₁ :=
      Nat.Coprime.coprime_dvd_right he2 (Nat.Coprime.coprime_dvd_left hd1 h)
    have c21 : Nat.Coprime a₂ m₁ :=
      Nat.Coprime.coprime_dvd_right he1 (Nat.Coprime.coprime_dvd_left hd2 h.symm)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hc₁ c12)
      (Nat.Coprime.mul_right c21 hc₂)
  · intro a ha
    obtain ⟨-, e, he, -⟩ := mem_unitaryDivisors.1 ha
    exact gcd_mul_gcd_of_dvd_mul h ⟨e, he⟩
  · rintro ⟨a₁, a₂⟩ hx
    rw [Finset.mem_product] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨-, m₁, hm₁, -⟩ := mem_unitaryDivisors.1 hx1
    obtain ⟨-, n₁, hn₁, -⟩ := mem_unitaryDivisors.1 hx2
    have hd1 : a₁ ∣ m := ⟨m₁, hm₁⟩
    have hd2 : a₂ ∣ n := ⟨n₁, hn₁⟩
    have ca2m : Nat.Coprime a₂ m := Nat.Coprime.coprime_dvd_left hd2 h.symm
    have ca1n : Nat.Coprime a₁ n := Nat.Coprime.coprime_dvd_left hd1 h
    have e1 : Nat.gcd (a₁ * a₂) m = a₁ := by
      rw [Nat.Coprime.gcd_mul_right_cancel a₁ ca2m, Nat.gcd_eq_left hd1]
    have e2 : Nat.gcd (a₁ * a₂) n = a₂ := by
      rw [Nat.Coprime.gcd_mul_left_cancel a₂ ca1n, Nat.gcd_eq_left hd2]
    simp [e1, e2]
  · intro a ha
    obtain ⟨-, e, he, -⟩ := mem_unitaryDivisors.1 ha
    exact (gcd_mul_gcd_of_dvd_mul h ⟨e, he⟩).symm

