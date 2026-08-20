import Mathlib

/-!
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- **Kraus maps are trace preserving.**
If a family of Kraus operators `E : K → Matrix n n ℂ` satisfies the completeness
relation `∑ k, (E k)ᴴ * E k = 1`, then the quantum channel
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace of every state `ρ`. -/
theorem kraus_trace_preserving
    {n K : Type*} [Fintype n] [Fintype K]
    (E : K → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) :
    (∑ k, E k * ρ * (E k)ᴴ).trace = ρ.trace := by
  classical
  have h1 : (∑ k, E k * ρ * (E k)ᴴ).trace = ∑ k, ((E k)ᴴ * E k * ρ).trace := by
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_cycle]
  rw [h1, ← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

end QC

