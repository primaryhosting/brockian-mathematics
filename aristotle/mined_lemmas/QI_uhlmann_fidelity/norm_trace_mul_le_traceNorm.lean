import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The dictionary between vectors of `H ⊗ H` and matrices

We model the Hilbert space `H` of a finite quantum system by `EuclideanSpace ℂ n` and the
composite system `H ⊗ H` by `EuclideanSpace ℂ (n × n)`.  A vector of the composite system is
the same thing as a matrix of coefficients. -/

/-- The matrix of coefficients of a vector of `H ⊗ H = EuclideanSpace ℂ (n × n)`. -/

theorem norm_trace_mul_le_traceNorm (M U : Matrix n n ℂ) (hU' : U * Uᴴ = 1) :
    ‖(M * U).trace‖ ≤ traceNorm M := by
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPpsd : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  set Q := CFC.sqrt P with hQdef
  have hQpsd : Q.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self _ hPpsd.nonneg
  have hQH : Qᴴ = Q := hQpsd.1
  -- the two Hilbert–Schmidt factors
  set X : Matrix n n ℂ := Q * Zᴴ with hXdef
  set Y : Matrix n n ℂ := Q * U with hYdef
  have hXH : Xᴴ = Z * Q := by
    rw [hXdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQH]
  have hXY : Xᴴ * Y = M * U := by
    rw [hXH, hYdef, hZ3, ← hQQ]
    simp [Matrix.mul_assoc]
  have hXX : (Xᴴ * X).trace = P.trace := by
    have h : Xᴴ * X = Z * P * Zᴴ := by
      rw [hXH, hXdef, ← hQQ]; simp [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_cycle, hZ1, Matrix.one_mul]
  have hYY : (Yᴴ * Y).trace = P.trace := by
    have h : Yᴴ * Y = Uᴴ * P * U := by
      rw [hYdef, Matrix.conjTranspose_mul, hQH, ← hQQ]; simp [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  have hnn : 0 ≤ P.trace.re := (trace_re_of_posSemidef hPpsd).2
  have h := norm_trace_le X Y
  rw [hXY, hXX, hYY, Real.mul_self_sqrt hnn] at h
  exact h

/-- The maximum in the variational characterisation of the trace norm is attained. -/
