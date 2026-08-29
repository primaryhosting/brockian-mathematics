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

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

private theorem eq_of_dvd_of_dvd_of_mul_eq {x y m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hx : x ∣ m) (hy : y ∣ n) (h : x * y = m * n) : x = m ∧ y = n := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hy0 : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have h2 : x * y * (s * t) = x * y * 1 := by rw [mul_one]; linarith [h]
  have hst : s * t = 1 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
  simp [Nat.eq_one_of_mul_eq_one_right hst, Nat.eq_one_of_mul_eq_one_left hst]

/-- `σ*` is multiplicative: `σ*(m n) = σ*(m) σ*(n)` for coprime positive `m, n`. -/
