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

open Polynomial

/-- The adjacency matrix of the cycle graph `C₄` (vertices `0-1-2-3-0`), as a real
`4 × 4` matrix.  This is the Hückel matrix of cyclobutadiene with `α = 0`, `β = 1`. -/

lemma huckelEigenvalue_three : huckelEigenvalue 3 = 0 := by
  simp only [huckelEigenvalue]
  norm_num
  rw [show (2 * Real.pi * 3 / 4 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add,
    Real.cos_pi_div_two]
  simp

/-- Each Hückel eigenvalue of `C₄` is one of `2`, `0`, `-2`. -/
