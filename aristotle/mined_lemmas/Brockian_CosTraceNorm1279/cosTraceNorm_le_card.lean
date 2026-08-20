import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

/-- The trace norm (sum of the absolute values of the eigenvalues) of the real diagonal
matrix `diagonal (fun i => cos (θ i))`. -/

theorem cosTraceNorm_le_card {n : ℕ} (θ : Fin n → ℝ) : cosTraceNorm θ ≤ (n : ℝ) := by
  have h : ∀ i ∈ Finset.univ, |Real.cos (θ i)| ≤ (1 : ℝ) := fun i _ =>
    Real.abs_cos_le_one (θ i)
  calc cosTraceNorm θ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum h
    _ = (n : ℝ) := by simp

/-- The bound is attained exactly when every angle is a multiple of `π`, i.e. `sin (θ i) = 0`. -/
