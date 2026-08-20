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

theorem trace_conj_contraction_le {P X : Matrix n n ℂ} (hP : P.PosSemidef)
    (hX : ∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Xᴴ y‖ ≤ ‖y‖) :
    (Matrix.trace (Xᴴ * P * X)).re ≤ (Matrix.trace P).re := by
  set Q := CFC.sqrt P with hQdef
  have hQh : Qᴴ = Q := (CFC.sqrt_nonneg P).posSemidef.1
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hP.nonneg
  have key : Matrix.trace (Xᴴ * P * X) = Matrix.trace ((Xᴴ * Q)ᴴ * (Xᴴ * Q)) := by
    have e1 : (Xᴴ * Q)ᴴ * (Xᴴ * Q) = Q * (X * Xᴴ * Q) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQh]
      noncomm_ring
    rw [e1, Matrix.trace_mul_comm Q (X * Xᴴ * Q), ← hQQ,
      Matrix.trace_mul_comm (Xᴴ * (Q * Q)) X]
    congr 1
    noncomm_ring
  rw [key, trace_conjTranspose_mul_self_re]
  have h2 : (Matrix.trace P).re = ∑ i : n, ‖Matrix.toEuclideanLin Q
      (EuclideanSpace.single i (1 : ℂ))‖ ^ 2 := by
    rw [← trace_conjTranspose_mul_self_re, hQh, hQQ]
  rw [h2]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [show Matrix.toEuclideanLin (Xᴴ * Q)
      = (Matrix.toEuclideanLin Xᴴ).comp (Matrix.toEuclideanLin Q) from
      Matrix.toLpLin_mul 2 2 2 _ _]
  simp only [LinearMap.comp_apply]
  gcongr
  exact hX _

/-- Duality bound for contractions: `|tr (M X)| ≤ tr √(Mᴴ M)` whenever `Xᴴ` is a
contraction. -/
