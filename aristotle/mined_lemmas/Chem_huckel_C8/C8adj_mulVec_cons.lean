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

lemma C8adj_mulVec_cons (a0 a1 a2 a3 a4 a5 a6 a7 : ℝ) :
    C8adj *ᵥ ![a0, a1, a2, a3, a4, a5, a6, a7] =
      ![a7 + a1, a0 + a2, a1 + a3, a2 + a4, a3 + a5, a4 + a6, a5 + a7, a6 + a0] := by
  funext i
  rw [C8adj_mulVec]
  fin_cases i <;> rfl

/-! ### The five distinct eigenvalues, with explicit eigenvectors -/

