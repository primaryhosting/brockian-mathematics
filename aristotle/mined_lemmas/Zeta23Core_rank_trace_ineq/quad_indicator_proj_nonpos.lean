import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

set_option maxHeartbeats 1000000

namespace Zeta23Core

variable {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius norm of a matrix: `‖M‖_F² = Re tr(Mᴴ M)`. -/

theorem quad_indicator_proj_nonpos [DecidableEq n] {U : Matrix n n 𝕜} (hU1 : Uᴴ * U = 1) (p : n → Prop)
    [DecidablePred p] (d : n → ℝ) (hd : ∀ i, ¬ p i → d i ≤ 0) (y : n → 𝕜)
    (hy : (U * diagonal (fun i => if p i then (1:𝕜) else 0) * Uᴴ) *ᵥ y = 0) :
    RCLike.re (star y ⬝ᵥ ((U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) *ᵥ y)) ≤ 0 := by
  set z : n → 𝕜 := Uᴴ *ᵥ y with hz
  have hzero : ∀ i, p i → z i = 0 := by
    have h1 : U *ᵥ (diagonal (fun i => if p i then (1:𝕜) else 0) *ᵥ z) = 0 := by
      simp only [hz, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact hy
    have h2 : diagonal (fun i => if p i then (1:𝕜) else 0) *ᵥ z = 0 := by
      have := congrArg (fun v => Uᴴ *ᵥ v) h1
      simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU1] using this
    intro i hi
    have := congrFun h2 i
    simpa [Matrix.mulVec_diagonal, hi] using this
  rw [quad_udu, map_sum]
  refine Finset.sum_nonpos fun i _ => ?_
  have hterm : (RCLike.ofReal ∘ d) i * (star (z i) * z i) = ((d i * ‖z i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul]
    simp [Function.comp]
  rw [hterm, RCLike.ofReal_re]
  by_cases h : p i
  · simp [hzero i h]
  · have := hd i h
    nlinarith [sq_nonneg ‖z i‖, norm_nonneg (z i)]

/-- If `B` annihilates a Hermitian matrix diagonalised as `U2 D U2ᴴ`, it annihilates the
spectral projection onto the nonzero part of its spectrum. -/
