import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
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

namespace Zeta23Core

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- The real quadratic form `x ↦ xᴴ Q x` attached to a matrix `Q`. -/

lemma qform_diagonal_nonpos (μ : m → ℝ) {y : m → 𝕜}
    (hy : y ∈ (coordKer (fun i => 0 < μ i) : Submodule 𝕜 (m → 𝕜))) :
    qform (Matrix.diagonal (RCLike.ofReal ∘ μ) : Matrix m m 𝕜) y ≤ 0 := by
  rw [mem_coordKer] at hy
  rw [qform_diagonal]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (μ i) with h | h
  · simp [hy i h]
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- Multiplication by an invertible matrix, as a linear equivalence. -/
