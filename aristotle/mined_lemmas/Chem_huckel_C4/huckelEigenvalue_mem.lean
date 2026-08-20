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

lemma huckelEigenvalue_mem (k : Fin 4) :
    huckelEigenvalue k = 2 ∨ huckelEigenvalue k = 0 ∨ huckelEigenvalue k = -2 := by
  fin_cases k
  · exact Or.inl huckelEigenvalue_zero
  · exact Or.inr (Or.inl huckelEigenvalue_one)
  · exact Or.inr (Or.inr huckelEigenvalue_two)
  · exact Or.inr (Or.inl huckelEigenvalue_three)

/-- `C4adj - μ • 1` written out explicitly. -/
