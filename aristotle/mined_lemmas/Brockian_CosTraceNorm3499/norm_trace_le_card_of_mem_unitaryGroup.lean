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

namespace Brockian

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix cosine of a complex square matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/

lemma norm_trace_le_card_of_mem_unitaryGroup {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U.trace‖ ≤ (Fintype.card n : ℝ) := by
  calc ‖U.trace‖ = ‖∑ i, U i i‖ := by rw [Matrix.trace]; rfl
    _ ≤ ∑ _i : n, (1 : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hU i i
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- **Trace-norm bound for the matrix cosine.**  For a Hermitian complex `n × n` matrix `A`,
the trace of `cos A` has modulus at most `n`. -/
