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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic definitions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr (Mᴴ M)`. -/

lemma frobSq_proj_comb {E F : Matrix n n 𝕜} (hEH : Eᴴ = E) (hFH : Fᴴ = F)
    (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0) (hFE : F * E = 0) (c d : ℝ) :
    frobSq ((c : 𝕜) • E + (d : 𝕜) • F)
      = c ^ 2 * RCLike.re E.trace + d ^ 2 * RCLike.re F.trace := by
  have hXH : (((c : 𝕜) • E + (d : 𝕜) • F))ᴴ = (c : 𝕜) • E + (d : 𝕜) • F := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hEH, hFH]
    simp
  rw [frobSq, hXH]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hEE, hFF, hEF, hFE,
    smul_zero, add_zero, zero_add, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, map_add, smul_smul]
  simp [RCLike.mul_re]
  ring

/-! ## The main inequality -/

/-- **Rank–trace inequality** (Lemma 3.2).  If `P` is positive semidefinite of rank at most `r`,
`Q` is Hermitian with at most `b` positive eigenvalues, and `c > 0`, then
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
