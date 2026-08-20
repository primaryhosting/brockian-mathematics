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

open Polynomial

/-- The adjacency matrix (Hückel matrix, in units where α = 0 and β = 1) of the cycle
graph `C₃`, over the reals. -/

theorem two_cos_C3 (k : Fin 3) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) = if k = 0 then 2 else -1 := by
  fin_cases k <;> norm_num
  · rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  · rw [show (2 : ℝ) * Real.pi * 2 / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_three]
    norm_num

/-- **Hückel theory for the cycle `C₃`.** A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₃` (i.e. there is a nonzero vector `v` with
`A v = μ v`) if and only if `μ = 2 cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
