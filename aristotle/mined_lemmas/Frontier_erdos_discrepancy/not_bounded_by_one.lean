/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The discrepancy sum of the sequence `f` along the homogeneous arithmetic progression
of common difference `d` and length `n`, i.e. `f d + f (2 d) + ... + f (n d)`. -/

private lemma not_bounded_by_one : False := by
  -- basic values, in terms of `a = f 1`
  have e2 : f 2 = -f 1 := by simpa using two_mul_eq hf h 1 one_pos (by norm_num)
  have e3 : f 3 = -f 1 := by simpa using three_mul_eq hf h 1 one_pos (by norm_num)
  have e5 : f 5 = -f 1 := by simpa using five_mul_eq hf h 1 one_pos (by norm_num)
  have e4 : f 4 = f 1 := by
    have := two_mul_eq hf h 2 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e2, neg_neg]
  have e6 : f 6 = f 1 := by
    have := two_mul_eq hf h 3 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e3, neg_neg]
  have e8 : f 8 = -f 1 := by
    have := two_mul_eq hf h 4 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e4]
  have e9 : f 9 = f 1 := by
    have := three_mul_eq hf h 3 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e3, neg_neg]
  have e10 : f 10 = f 1 := by
    have := two_mul_eq hf h 5 (by norm_num) (by norm_num)
    norm_num at this
    rw [this, e5, neg_neg]
  -- the length-8 progression forces `f 7 = f 1`
  have h8 := h 1 8 one_pos (by norm_num) (by norm_num)
  have E8 : apSum f 1 8 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  rw [E8, e2, e3, e4, e5, e6, e8] at h8
  have hsum : |f 7 + -f 1| ≤ 1 := by
    have : f 1 + -f 1 + -f 1 + f 1 + -f 1 + f 1 + f 7 + -f 1 = f 7 + -f 1 := by ring
    rwa [this] at h8
  have e7 : f 7 = f 1 := by
    rcases hf 1 one_pos with h1 | h1 <;> rcases hf 7 (by norm_num) with h7 | h7 <;>
      rw [h1, h7] at hsum <;> simp_all
  -- now the length-10 progression has discrepancy `2`
  have h10 := h 1 10 one_pos (by norm_num) (by norm_num)
  have E10 : apSum f 1 10 =
      f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  rw [E10, e2, e3, e4, e5, e6, e7, e8, e9, e10] at h10
  have hfin : |2 * f 1| ≤ 1 := by
    have : f 1 + -f 1 + -f 1 + f 1 + -f 1 + f 1 + f 1 + -f 1 + f 1 + f 1 = 2 * f 1 := by ring
    rwa [this] at h10
  rcases hf 1 one_pos with h1 | h1 <;> rw [h1] at hfin <;> norm_num at hfin

end Base

/-- **Erdős discrepancy problem, base case `C = 1`.**
For every `±1` sequence `f` there are a positive common difference `d` and a positive
length `n`, with all the used indices at most `12`, such that the discrepancy
`|f d + f (2 d) + ⋯ + f (n d)|` exceeds `1`.
(The full statement of Tao's theorem, that the discrepancy is unbounded, is recorded
as `Frontier.UnboundedDiscrepancy`; this is its `C = 1` case, made quantitative.
The bound `12` is optimal, see `Frontier.erdos_discrepancy_sharp`.) -/
