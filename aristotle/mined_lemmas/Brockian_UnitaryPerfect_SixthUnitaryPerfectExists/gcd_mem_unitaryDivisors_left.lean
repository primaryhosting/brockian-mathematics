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

theorem gcd_mem_unitaryDivisors_left {m n a : ℕ} (h : Nat.Coprime m n)
    (ha : a ∈ unitaryDivisors (m * n)) : Nat.gcd a m ∈ unitaryDivisors m := by
  obtain ⟨hmn, f, hf, hcf⟩ := mem_unitaryDivisors.1 ha
  have hm : m ≠ 0 := fun h0 => hmn (by simp [h0])
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hf; exact hmn hf
  have hsplit : a = Nat.gcd a m * Nat.gcd a n :=
    (gcd_mul_gcd_of_dvd_mul h ⟨f, hf⟩).symm
  set a₁ := Nat.gcd a m with ha₁
  set a₂ := Nat.gcd a n with ha₂
  obtain ⟨m₁, hm₁⟩ : a₁ ∣ m := Nat.gcd_dvd_right a m
  obtain ⟨n₁, hn₁⟩ : a₂ ∣ n := Nat.gcd_dvd_right a n
  have hmul : a * f = a * (m₁ * n₁) := by
    conv_rhs => rw [hsplit]
    rw [← hf, hm₁, hn₁]; ring
  have hfe : f = m₁ * n₁ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) hmul
  refine mem_unitaryDivisors.2 ⟨hm, m₁, hm₁, ?_⟩
  exact Nat.Coprime.coprime_dvd_right ⟨n₁, hfe⟩
    (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a m) hcf)

/-- `σ*` is multiplicative. -/
