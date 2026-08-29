/-
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Kraus (operator-sum) representation of a quantum channel:
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ`. -/
noncomputable def krausMap {n : Type*} [Fintype n] [DecidableEq n]
    {κ : Type*} [Fintype κ] (E : κ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  ∑ k, E k * ρ * (E k)ᴴ

/-- **Kraus maps are trace preserving.**
If the Kraus operators satisfy the completeness relation `∑ k, (E k)ᴴ * E k = 1`,
then the associated CPTP map `ρ ↦ ∑ k, E k ρ (E k)ᴴ` preserves the trace.

The proof uses cyclicity of the trace (`Matrix.trace_mul_cycle`) to rewrite each
summand `tr (E k ρ (E k)ᴴ)` as `tr ((E k)ᴴ (E k) ρ)`, then linearity of matrix
multiplication (`Matrix.sum_mul`) together with the completeness relation, and
finally `Matrix.one_mul`. -/
theorem kraus_trace_preserving {n : Type*} [Fintype n] [DecidableEq n]
    {κ : Type*} [Fintype κ] (E : κ → Matrix n n ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (ρ : Matrix n n ℂ) :
    (krausMap E ρ).trace = ρ.trace := by
  unfold krausMap
  rw [Matrix.trace_sum]
  have h1 : ∀ k : κ, (E k * ρ * (E k)ᴴ).trace = ((E k)ᴴ * E k * ρ).trace := by
    intro k
    rw [Matrix.trace_mul_cycle]
  calc ∑ k, (E k * ρ * (E k)ᴴ).trace
      = ∑ k, ((E k)ᴴ * E k * ρ).trace := Finset.sum_congr rfl fun k _ => h1 k
    _ = ((∑ k, (E k)ᴴ * E k) * ρ).trace := by rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [hE, Matrix.one_mul]

end QC

