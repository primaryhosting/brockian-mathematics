import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma abs_sum_sub_card_mul_le {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ)
    (h : ∀ T ∈ s, |f T - c| ≤ 1) : |(∑ T ∈ s, f T) - s.card * c| ≤ s.card := by
  have heq : (∑ T ∈ s, f T) - s.card * c = ∑ T ∈ s, (f T - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [heq]
  calc |∑ T ∈ s, (f T - c)| ≤ ∑ T ∈ s, |f T - c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ s, (1 : ℝ) := Finset.sum_le_sum h
    _ = s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Main counting estimate. -/
