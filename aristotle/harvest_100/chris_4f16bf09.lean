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

import Mathlib
/-!
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Finset

/-- A quantum channel in Kraus form, `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ`. -/
noncomputable def krausMap {K n : Type*} [Fintype K] [Fintype n] [DecidableEq n]
    (E : K → Matrix n n ℂ) (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, E k * ρ * (E k)ᴴ

/-- **Kraus maps are trace preserving.**  If the Kraus operators `E k` satisfy the
completeness relation `∑ k, (E k)ᴴ * E k = 1`, then the associated channel
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace of every matrix `ρ`. -/
theorem kraus_trace_preserving {K n : Type*} [Fintype K] [Fintype n] [DecidableEq n]
    (E : K → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (ρ : Matrix n n ℂ) :
    (krausMap E ρ).trace = ρ.trace := by
  unfold krausMap
  rw [trace_sum]
  have h1 : ∀ k, (E k * ρ * (E k)ᴴ).trace = ((E k)ᴴ * E k * ρ).trace := by
    intro k
    rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
  simp_rw [h1]
  rw [← trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

/-- A Kraus channel satisfying the completeness relation maps normalized states
(`trace ρ = 1`) to normalized states. -/
theorem kraus_trace_one {K n : Type*} [Fintype K] [Fintype n] [DecidableEq n]
    (E : K → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (ρ : Matrix n n ℂ)
    (hρ : ρ.trace = 1) : (krausMap E ρ).trace = 1 := by
  rw [kraus_trace_preserving E hE ρ, hρ]

end QC

