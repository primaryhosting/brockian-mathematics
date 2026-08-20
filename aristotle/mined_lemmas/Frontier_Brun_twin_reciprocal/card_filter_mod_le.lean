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

lemma card_filter_mod_le (N m r : ℕ) :
    ((range N).filter (fun n => n % m = r)).card ≤ N / m + 1 := by
  have h : ((range N).filter (fun n => n % m = r)).card ≤ (range (N / m + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_range]
      have : n / m ≤ N / m := Nat.div_le_div_right hn.1.le
      omega
    · intro n hn n' hn' h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn hn'
      simp only at h
      have e1 := Nat.div_add_mod n m
      have e2 := Nat.div_add_mod n' m
      rw [hn.2] at e1
      rw [hn'.2] at e2
      rw [h] at e1
      omega
  simpa using h

/-- Counting a residue class in `range N`: lower bound. -/
