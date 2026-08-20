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

lemma qform_diagonal (μ : m → ℝ) (y : m → 𝕜) :
    qform (Matrix.diagonal (RCLike.ofReal ∘ μ) : Matrix m m 𝕜) y = ∑ i, μ i * ‖y i‖ ^ 2 := by
  unfold qform
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  have hstep : star (y i) * ((RCLike.ofReal ∘ μ) i * y i) = ((μ i * ‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    have h := RCLike.conj_mul (y i)
    simp only [Function.comp_apply, RCLike.star_def]
    rw [show (RCLike.ofReal (μ i) * y i) = y i * RCLike.ofReal (μ i) from mul_comm _ _,
      ← mul_assoc, h]
    push_cast
    ring
  rw [Pi.star_apply, hstep, RCLike.ofReal_re]

