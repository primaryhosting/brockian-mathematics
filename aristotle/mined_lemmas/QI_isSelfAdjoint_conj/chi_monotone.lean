import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem chi_monotone {t : ℝ} (ht : 0 < t) {ι : Type u} [Fintype ι] {K : ι → Matrix m n ℂ}
    (hK : ∑ a, (K a)ᴴ * K a = 1) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hKP : (krausMap K P).PosDef) (hKQ : (krausMap K Q).PosDef) :
    chi t hKP.1 hKQ.1 ≤ chi t hP.1 hQ.1 := by
  set W := sylv t hKP.1 hKQ.1 with hW
  set Y := krausAdj K W with hY
  have hYH : Yᴴ = krausAdj K Wᴴ := krausAdj_conjTranspose K W
  have ha : (Matrix.trace (Wᴴ * (krausMap K P - krausMap K Q))).re
      = (Matrix.trace (Yᴴ * (P - Q))).re := by
    rw [← krausMap_sub, Matrix.trace_mul_comm, trace_krausMap_mul, ← hYH, Matrix.trace_mul_comm]
  have hb1 : (Matrix.trace (Yᴴ * P * Y)).re ≤ (Matrix.trace (Wᴴ * krausMap K P * W)).re := by
    have e1 : (Matrix.trace (Yᴴ * P * Y)).re = (Matrix.trace (P * (Y * Yᴴ))).re := by
      congr 1
      rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    have e2 : (Matrix.trace (Wᴴ * krausMap K P * W)).re
        = (Matrix.trace (P * krausAdj K (W * Wᴴ))).re := by
      congr 1
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm, trace_krausMap_mul]
    have hpsd : (krausAdj K (W * Wᴴ) - Y * Yᴴ).PosSemidef := by
      have h := krausAdj_schwarz hK Wᴴ
      rw [Matrix.conjTranspose_conjTranspose, ← hYH, Matrix.conjTranspose_conjTranspose] at h
      exact h
    rw [e1, e2]
    exact trace_mul_mono hP.posSemidef hpsd
  have hb2 : (Matrix.trace (Yᴴ * Y * Q)).re ≤ (Matrix.trace (Wᴴ * W * krausMap K Q)).re := by
    have e1 : (Matrix.trace (Yᴴ * Y * Q)).re = (Matrix.trace (Q * (Yᴴ * Y))).re := by
      congr 1
      rw [Matrix.trace_mul_comm]
    have e2 : (Matrix.trace (Wᴴ * W * krausMap K Q)).re
        = (Matrix.trace (Q * krausAdj K (Wᴴ * W))).re := by
      congr 1
      rw [Matrix.trace_mul_comm, trace_krausMap_mul]
    have hpsd : (krausAdj K (Wᴴ * W) - Yᴴ * Y).PosSemidef := by
      have h := krausAdj_schwarz hK W
      rw [← hY] at h
      exact h
    rw [e1, e2]
    exact trace_mul_mono hQ.posSemidef hpsd
  have hb : quadForm t P Q Y ≤ quadForm t (krausMap K P) (krausMap K Q) W := by
    unfold quadForm
    have := mul_le_mul_of_nonneg_left hb1 ht.le
    linarith
  have hce := chi_eq ht hKP hKQ
  have hle := le_chi ht hP hQ Y
  rw [← hW] at hce
  rw [hce, ha]
  linarith

/-! ### The scalar integral -/

/-- The antiderivative of the scalar integrand. -/
private noncomputable def scalarPrim (p q s : ℝ) : ℝ :=
  p * Real.log (s * p + q) - p * Real.log (1 + s) + (p - q) / (1 + s)

