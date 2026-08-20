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

lemma le_card_filter_mod (N m r : ℕ) (hr : r < m) :
    N / m ≤ ((range N).filter (fun n => n % m = r)).card := by
  have h : (range (N / m)).card ≤ ((range N).filter (fun n => n % m = r)).card := by
    refine Finset.card_le_card_of_injOn (fun q => q * m + r) ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_range] at hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, by simp [Nat.mod_eq_of_lt hr]⟩
      have h1 : (q + 1) * m ≤ (N / m) * m := Nat.mul_le_mul_right m hq
      have h2 : (N / m) * m ≤ N := Nat.div_mul_le_self N m
      have : q * m + m ≤ N := by nlinarith [h1, h2]
      omega
    · intro q _ q' _ h
      simp only at h
      have hm : 0 < m := by omega
      have : q * m = q' * m := by omega
      exact Nat.eq_of_mul_eq_mul_right hm this
  simpa using h

