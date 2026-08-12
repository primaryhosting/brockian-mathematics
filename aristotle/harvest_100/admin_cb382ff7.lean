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

namespace QC

open Matrix

/-- **Kraus maps are trace preserving.**
If a family of Kraus operators `E k : Matrix n n ℂ` satisfies the completeness
relation `∑ k, (E k)ᴴ * E k = 1`, then the associated quantum channel
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace. -/
theorem kraus_trace_preserving {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    (E : κ → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = (1 : Matrix n n ℂ)) :
    Matrix.trace (∑ k, E k * ρ * (E k)ᴴ) = Matrix.trace ρ := by
  have key : ∀ k, Matrix.trace (E k * ρ * (E k)ᴴ) = Matrix.trace ((E k)ᴴ * E k * ρ) := by
    intro k
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  calc Matrix.trace (∑ k, E k * ρ * (E k)ᴴ)
      = ∑ k, Matrix.trace ((E k)ᴴ * E k * ρ) := by
        rw [Matrix.trace_sum]
        exact Finset.sum_congr rfl (fun k _ => key k)
    _ = Matrix.trace ((∑ k, (E k)ᴴ * E k) * ρ) := by
        rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace ρ := by rw [hE, Matrix.one_mul]

#print axioms QC.kraus_trace_preserving

end QC

