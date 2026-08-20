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

theorem norm_trace_mul_contraction_le (M X : Matrix n n ℂ)
    (hX : ∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Xᴴ y‖ ≤ ‖y‖) :
    ‖Matrix.trace (M * X)‖ ≤ (Matrix.trace (CFC.sqrt (Mᴴ * M))).re := by
  obtain ⟨W, hW, hM⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPpsd : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  set Q := CFC.sqrt P with hQdef
  have hQh : Qᴴ = Q := (CFC.sqrt_nonneg P).posSemidef.1
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hPpsd.nonneg
  have hWstar' : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have htr : Matrix.trace (M * X) = Matrix.trace (Qᴴ * (Q * X * W)) := by
    rw [hM, hQh]
    rw [show W * P * X = W * (Q * (Q * X)) by rw [← hQQ]; noncomm_ring]
    rw [Matrix.trace_mul_comm W (Q * (Q * X))]
    congr 1
    noncomm_ring
  have h1 : Matrix.trace (Qᴴ * Q) = Matrix.trace P := by rw [hQh, hQQ]
  have h2 : Matrix.trace ((Q * X * W)ᴴ * (Q * X * W)) = Matrix.trace (Xᴴ * P * X) := by
    have e1 : (Q * X * W)ᴴ * (Q * X * W) = Wᴴ * ((Xᴴ * P * X) * W) := by
      simp only [Matrix.conjTranspose_mul, hQh]
      rw [← hQQ]; noncomm_ring
    rw [e1, Matrix.trace_mul_comm Wᴴ ((Xᴴ * P * X) * W), Matrix.mul_assoc, hWstar',
      Matrix.mul_one]
  have hnn : (0:ℝ) ≤ (Matrix.trace P).re := by
    have hle := hPpsd.trace_nonneg
    simpa using (Complex.le_def.mp hle).1
  calc ‖Matrix.trace (M * X)‖
      = ‖Matrix.trace (Qᴴ * (Q * X * W))‖ := by rw [htr]
    _ ≤ Real.sqrt (Matrix.trace (Qᴴ * Q)).re *
          Real.sqrt (Matrix.trace ((Q * X * W)ᴴ * (Q * X * W))).re :=
        norm_trace_conjTranspose_mul_le _ _
    _ ≤ Real.sqrt (Matrix.trace P).re * Real.sqrt (Matrix.trace P).re := by
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (trace_conj_contraction_le hPpsd hX)) (Real.sqrt_nonneg _)
    _ = (Matrix.trace P).re := Real.mul_self_sqrt hnn

/-- The fidelity dominates the overlap of any two purifications, with an ancilla of
arbitrary dimension (matrix form). -/
