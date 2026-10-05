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

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.GoldbachComb

/-! ## Primality (self-contained, no imports) -/

/-- `IsPrime p` : `p` is at least `2` and has no divisors other than `1` and `p`. -/

theorem isPrime_of_primeB {p : Nat} (h : primeB p = true) : IsPrime p := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, List.mem_range] at h
  obtain ⟨h2, hall⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  have hp0 : 0 < p := by omega
  have hmle : m ≤ p := Nat.le_of_dvd hp0 hm
  have hmlt : m < p := by omega
  obtain ⟨k, rfl⟩ := hm
  have hmod : m * k % m = 0 := Nat.mul_mod_right m k
  have h3 := hall m hmlt
  simp [hmod] at h3
  have hm0 : m = 0 := by omega
  subst hm0
  simp at h2

/-! ## The Goldbach counting function -/

/-- The list of `p ≤ n` such that both `p` and `n - p` pass the primality test. -/
