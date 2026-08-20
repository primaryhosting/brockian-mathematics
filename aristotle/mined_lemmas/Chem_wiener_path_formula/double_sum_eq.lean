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

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all
unordered pairs of distinct vertices (represented as ordered pairs `u < v`). -/

lemma double_sum_eq (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, (if a < b then b - a else 0)
      = (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : ∑ b ∈ Finset.range (n + 1), (if n < b then b - n else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      simp only [Finset.mem_range] at hb
      rw [if_neg (by omega)]
    have h3 : ∀ a ∈ Finset.range n,
        ∑ b ∈ Finset.range (n + 1), (if a < b then b - a else 0)
          = (∑ b ∈ Finset.range n, (if a < b then b - a else 0)) + (n - a) := by
      intro a ha
      simp only [Finset.mem_range] at ha
      rw [Finset.sum_range_succ, if_pos ha]
    rw [h2, add_zero, Finset.sum_congr rfl h3, Finset.sum_add_distrib, ih, sum_range_sub,
      Nat.choose_succ_succ (n + 1) 2]
    norm_num
    omega

/-- **Wiener index of the path graph**: `W(P_n) = C(n+1, 3)`. -/
