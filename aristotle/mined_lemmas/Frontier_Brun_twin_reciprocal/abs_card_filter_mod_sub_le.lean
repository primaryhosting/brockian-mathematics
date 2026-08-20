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

lemma abs_card_filter_mod_sub_le (N m r : ℕ) (hr : r < m) :
    |(((range N).filter (fun n => n % m = r)).card : ℝ) - (N : ℝ) / m| ≤ 1 := by
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := card_filter_mod_le N m r
  have h2 := le_card_filter_mod N m r hr
  have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hfl2 : (N : ℝ) / m < ((N / m : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hmR]
    have hdm := Nat.div_add_mod N m
    have hlt := Nat.mod_lt N hm
    have : N < (N / m + 1) * m := by
      have : (N / m + 1) * m = m * (N / m) + m := by ring
      omega
    exact_mod_cast this
  have h1R : (((range N).filter (fun n => n % m = r)).card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1
  have h2R : ((N / m : ℕ) : ℝ) ≤ (((range N).filter (fun n => n % m = r)).card : ℝ) := by
    exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- The number of `n < N` in a fixed pair of coprime congruence conditions. -/
