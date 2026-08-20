import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/

theorem normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  obtain ⟨h1, h2⟩ := hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h : (W * star W) i i = (1 : Matrix (Fin d) (Fin d) ℂ) i i := by rw [h2]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq, Complex.mul_conj] at h
    exact_mod_cast (by exact_mod_cast h : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = 1)
  · have h : (star W * W) j j = (1 : Matrix (Fin d) (Fin d) ℂ) j j := by rw [h1]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq,
      ← Complex.normSq_eq_conj_mul_self] at h
    exact_mod_cast (by exact_mod_cast h : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = 1)

/-- Simultaneous diagonalisation step: the trace of a product of two Hermitian matrices is the
trace of `Dₐ W D_b W*`, where `W` is the unitary relating the two eigenbases. -/
