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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

/-- Birkhoff + rearrangement: for antitone `mu`, `nu` and a doubly stochastic matrix `S`,
the bilinear form `∑ i j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`. -/

lemma sq_abs_mem_doublyStochastic {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun i j => ‖W i j‖ ^ 2) ∈ doublyStochastic ℝ (Fin d) := by
  have hnorm : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ) ^ 2 := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h1 : W * Wᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).1 hW
  have h2 : Wᴴ * W = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hW
  rw [mem_doublyStochastic_iff_sum]
  simp only [Matrix.of_apply]
  refine ⟨fun i j => by positivity, fun i => ?_, fun j => ?_⟩
  · have h : ((∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      have hii := congrFun (congrFun h1 i) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hii
      rw [← hii]
      exact Finset.sum_congr rfl fun j _ => by rw [Complex.star_def, hnorm]
    exact_mod_cast h
  · have h : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      have hjj := congrFun (congrFun h2 j) j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hjj
      rw [← hjj]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.star_def, mul_comm, hnorm]
    exact_mod_cast h

/-- The trace of `diagonal mu * W * diagonal nu * Wᴴ` in terms of the squared moduli of `W`. -/
