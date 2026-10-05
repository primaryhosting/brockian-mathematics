/-
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

If `E : κ → Matrix n n ℂ` is a family of Kraus operators satisfying the
completeness relation `∑ k, (E k)ᴴ * (E k) = 1`, then the associated quantum
channel `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace.

The key ingredient from Mathlib is `Matrix.trace_mul_cycle`, which gives
`trace (E * ρ * Eᴴ) = trace (Eᴴ * E * ρ)`; summing over `k` and using the
completeness relation finishes the proof. -/
theorem kraus_trace_preserving {n : Type*} [Fintype n] [DecidableEq n]
    {κ : Type*} [Fintype κ] (E : κ → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) :
    Matrix.trace (∑ k, E k * ρ * (E k)ᴴ) = Matrix.trace ρ := by
  rw [Matrix.trace_sum]
  have h : ∀ k : κ, Matrix.trace (E k * ρ * (E k)ᴴ)
      = Matrix.trace ((E k)ᴴ * E k * ρ) := by
    intro k
    rw [Matrix.trace_mul_cycle]
  simp_rw [h, ← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

end QC

