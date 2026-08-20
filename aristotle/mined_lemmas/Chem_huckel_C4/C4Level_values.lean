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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₄`,
i.e. of cyclobutadiene. -/

lemma C4Level_values :
    C4Level 0 = 2 ∧ C4Level 1 = 0 ∧ C4Level 2 = -2 ∧ C4Level 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [C4Level] <;> norm_num
  · rw [show (2 : ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]
  · rw [show (2 : ℝ) * Real.pi * 2 / 4 = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [show (2 : ℝ) * Real.pi * 3 / 4 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
    ring

/-- **Hückel theory for cyclobutadiene (`C₄`).**  The characteristic polynomial of the
adjacency matrix of the cycle graph `C₄` factors as `∏ k, (X - 2 cos (2πk/4))`; equivalently,
the adjacency eigenvalues of `C₄`, with multiplicity, are `2 cos (2πk/4)` for `k = 0, 1, 2, 3`. -/
