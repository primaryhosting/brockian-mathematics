import Mathlib
/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/

lemma normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun i j => ‖W i j‖ ^ 2) ∈ doublyStochastic ℝ (Fin d) := by
  have h1 : star W * W = 1 := hW.1
  have h2 : W * star W = 1 := hW.2
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp, fun i => ?_, fun j => ?_⟩
  · have hi := congrFun (congrFun h2 i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hi
    have hcast : ((∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← hi]
      exact Finset.sum_congr rfl fun j _ => (mul_star_eq_normSq (W i j)).symm
    exact_mod_cast hcast
  · have hj := congrFun (congrFun h1 j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hj
    have hcast : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      exact (mul_star_eq_normSq (W i j)).symm
    exact_mod_cast hcast

/-- Trace of `diagonal a * W * diagonal b * star W` in terms of squared moduli of the entries
of `W`. -/
