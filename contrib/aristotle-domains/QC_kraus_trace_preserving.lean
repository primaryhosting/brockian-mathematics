/-!
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Statement: A CPTP map Σ_k E_k ρ E_k† with Σ_k E_k†E_k = I preserves trace.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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
If `E : K → Matrix n n ℂ` is a family of Kraus operators satisfying the
completeness relation `∑ k, (E k)ᴴ * (E k) = 1`, then the associated quantum
channel `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace. -/
theorem kraus_trace_preserving {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (E : K → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (ρ : Matrix n n ℂ) :
    (∑ k, E k * ρ * (E k)ᴴ).trace = ρ.trace := by
  rw [Matrix.trace_sum]
  have h : ∀ k : K, (E k * ρ * (E k)ᴴ).trace = ((E k)ᴴ * E k * ρ).trace := by
    intro k
    rw [Matrix.trace_mul_comm (E k * ρ) ((E k)ᴴ), Matrix.mul_assoc]
  simp_rw [h]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

end QC

