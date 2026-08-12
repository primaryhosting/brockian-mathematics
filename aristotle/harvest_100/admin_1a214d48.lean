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

/-
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Finset

/-- A quantum channel in Kraus form, `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ`, whose Kraus
operators satisfy the completeness relation `∑ k, (E k)ᴴ * E k = 1`, preserves
the trace.

The key Mathlib ingredients are `Matrix.trace_mul_comm` (cyclicity of the trace)
and `Matrix.trace_sum`. -/
theorem kraus_trace_preserving {n : Type*} [Fintype n] [DecidableEq n]
    {ι : Type*} [Fintype ι] (E : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) :
    trace (∑ k, E k * ρ * (E k)ᴴ) = trace ρ := by
  rw [trace_sum]
  have h : ∀ k, trace (E k * ρ * (E k)ᴴ) = trace ((E k)ᴴ * E k * ρ) := by
    intro k
    rw [trace_mul_comm, Matrix.mul_assoc]
  simp only [h]
  rw [← trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

end QC

