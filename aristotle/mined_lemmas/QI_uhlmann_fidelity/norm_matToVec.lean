/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/

theorem norm_matToVec {m : Type*} [Fintype m] (A : Matrix n m ℂ) :
    ‖matToVec A‖ = Real.sqrt (Matrix.trace (Aᴴ * A)).re := by
  have h : ‖matToVec A‖ ^ 2 = (Matrix.trace (Aᴴ * A)).re := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [matToVec, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diag_apply, ← Finset.sum_product', Complex.re_sum, Complex.mul_re,
      WithLp.ofLp_toLp, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Fintype.sum_equiv (Equiv.prodComm n m) _ _ (fun p => ?_)
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq n] in
/-- The reduced density matrix of the purification associated to `A` is `A Aᴴ`. -/
