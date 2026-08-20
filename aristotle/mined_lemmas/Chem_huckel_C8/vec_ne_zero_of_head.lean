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

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma vec_ne_zero_of_head {a0 a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : a0 ≠ 0) :
    ![a0, a1, a2, a3, a4, a5, a6, a7] ≠ 0 := by
  intro hc
  exact h (by simpa using congrFun hc 0)

