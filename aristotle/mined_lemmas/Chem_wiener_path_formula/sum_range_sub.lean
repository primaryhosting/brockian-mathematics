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

lemma sum_range_sub (n : ℕ) : ∑ a ∈ Finset.range n, (n - a) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : ∀ a ∈ Finset.range n, n + 1 - a = (n - a) + 1 := by
      intro a ha
      simp only [Finset.mem_range] at ha
      omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, ih,
      Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
    norm_num
    omega

