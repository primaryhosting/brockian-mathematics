import Mathlib
/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of `W`. If `W` is unitary this is a doubly
stochastic matrix. -/

lemma re_trace_diag_mul {a b : n → ℝ} (W : Matrix n n 𝕜) :
    RCLike.re (Matrix.trace (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * W *
        diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star W))
      = ∑ j, ∑ k, a j * b k * weightMatrix W j k := by
  have hz : ∀ z : 𝕜, z * star z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    intro z; rw [RCLike.star_def, RCLike.mul_conj]; push_cast; ring
  have hd : ∀ j : n, (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * W *
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star W) j j
      = ((∑ k, a j * b k * weightMatrix W j k : ℝ) : 𝕜) := by
    intro j
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
    simp only [Function.comp_apply, weightMatrix_apply]
    rw [show (a j : 𝕜) * W j k * (b k : 𝕜) * star (W j k)
        = ((a j : 𝕜) * (b k : 𝕜)) * (W j k * star (W j k)) by ring, hz]
  simp only [Matrix.trace, Matrix.diag_apply, hd, ← RCLike.ofReal_sum, RCLike.ofReal_re]

/-- Von Neumann's trace inequality in diagonalized form: if `U` and `V` are unitary and the
real vectors `a` and `b` monovary, then `Re tr (U diag(a) Uᴴ V diag(b) Vᴴ) ≤ ∑ᵢ aᵢ bᵢ`. -/
