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

theorem trace_conjTranspose_mul_self_re (Y : Matrix n m ℂ) :
    (Matrix.trace (Yᴴ * Y)).re
      = ∑ i : m, ‖Matrix.toEuclideanLin Y (EuclideanSpace.single i (1 : ℂ))‖ ^ 2 := by
  have h1 : ∀ i : m, ‖Matrix.toEuclideanLin Y (EuclideanSpace.single i (1 : ℂ))‖ ^ 2
      = ∑ j : n, ‖Y j i‖ ^ 2 := by
    intro i
    rw [Matrix.toLpLin_apply, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    congr 1
    ext j
    simp [Matrix.mulVec_single]
  simp only [h1, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diag_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- For a positive semidefinite `P` and a matrix `X` whose adjoint is a contraction,
`tr (Xᴴ P X) ≤ tr P`. -/
