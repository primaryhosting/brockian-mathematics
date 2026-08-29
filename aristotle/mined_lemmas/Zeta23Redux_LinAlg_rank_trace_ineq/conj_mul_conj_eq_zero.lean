import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/

lemma conj_mul_conj_eq_zero {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (f g : Fin d → ℝ)
    (hfg : ∀ i, f i * g i = 0) :
    (U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ) *
      (U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ) = 0 := by
  have h : (U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ) *
      (U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ)
      = U * (Matrix.diagonal (fun i => (f i : ℂ)) * ((Uᴴ * U) *
        Matrix.diagonal (fun i => (g i : ℂ)))) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, hU, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  have hz : (fun i => (f i : ℂ) * (g i : ℂ)) = fun _ => (0 : ℂ) := by
    funext i; rw [← Complex.ofReal_mul, hfg i]; simp
  rw [hz]
  simp

/-- Spectral theorem, in the explicit form `A = U D Uᴴ`. -/
