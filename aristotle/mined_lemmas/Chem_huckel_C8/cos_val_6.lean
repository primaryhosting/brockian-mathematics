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

lemma cos_val_6 : 2 * Real.cos (2 * Real.pi * ((6 : ℕ) : ℝ) / 8) = 0 := by
  rw [show 2 * Real.pi * ((6 : ℕ) : ℝ) / 8 = Real.pi + Real.pi / 2 by push_cast; ring,
    Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

