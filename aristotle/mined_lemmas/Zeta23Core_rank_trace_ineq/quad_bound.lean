/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Basic notions -/

/-- The real part of the trace of a matrix. -/

lemma quad_bound {M : Matrix n n 𝕜} (hM : M.IsHermitian) (hE : E.IsHermitian) (hE2 : E * E = E)
    {t : ℝ} (ht : 0 < t) (hneg : rtr ((1 - E) * M * (1 - E)) ≤ 0) :
    2 * t * rtr M - t ^ 2 * rtr E ≤ froSq M := by
  have hXh : ((t : 𝕜) • E).IsHermitian := by
    show ((t : 𝕜) • E)ᴴ = (t : 𝕜) • E
    rw [Matrix.conjTranspose_smul, hE.eq]
    simp
  have hfroX : froSq ((t : 𝕜) • E) = t ^ 2 * rtr E := by
    rw [froSq, hXh.eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← RCLike.ofReal_mul,
      rtr_smul, hE2]
    ring
  have hMX : rtr (M * ((t : 𝕜) • E)) = t * rtr (M * E) := by
    rw [Matrix.mul_smul, rtr_smul]
  have hkey : rtr M ≤ rtr (M * E) := by
    have h1 : rtr ((1 - E) * M * (1 - E)) = rtr M - rtr (M * E) := by
      rw [rtr_conj_proj (proj_compl_sq hE2), Matrix.mul_sub, Matrix.mul_one, rtr_sub]
    linarith [hneg, h1.symm.trans_le hneg]
  have hmain := two_mul_rtr_mul_le hM hXh
  rw [hMX, hfroX] at hmain
  have : 2 * t * rtr M ≤ 2 * t * rtr (M * E) := by
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ 2 * t)
    linarith
  linarith

/-! ### Spectral projections -/

