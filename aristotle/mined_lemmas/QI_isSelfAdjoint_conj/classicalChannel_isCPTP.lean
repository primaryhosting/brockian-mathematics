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

theorem classicalChannel_isCPTP {m : Type u} [Fintype m] [DecidableEq m] {T : m → n → ℝ}
    (hT : ∀ j i, 0 ≤ T j i) (hTcol : ∀ i, ∑ j, T j i = 1) : IsCPTP (classicalChannel T) := by
  refine ⟨m × n, inferInstance,
    fun a => Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ), ?_, ?_⟩
  · have h : ∀ a : m × n,
        (Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ))ᴴ
          * Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ)
        = Matrix.single a.2 a.2 ((T a.1 a.2 : ℝ) : ℂ) := by
      rintro ⟨j, i⟩
      rw [single_conjTranspose, Matrix.single_mul_single_same]
      congr 1
      have : ((Real.sqrt (T j i) : ℝ) : ℂ) * ((Real.sqrt (T j i) : ℝ) : ℂ)
          = ((Real.sqrt (T j i) * Real.sqrt (T j i) : ℝ) : ℂ) := by push_cast; ring
      rw [RCLike.star_def, Complex.conj_ofReal, this, Real.mul_self_sqrt (hT j i)]
    rw [Finset.sum_congr rfl (fun a _ => h a), Fintype.sum_prod_type, Finset.sum_comm]
    have h2 : ∀ i : n, ∑ j : m, Matrix.single i i ((T j i : ℝ) : ℂ)
        = Matrix.single i i (1 : ℂ) := by
      intro i
      rw [sum_single_const]
      congr 1
      rw [← Complex.ofReal_sum, hTcol i, Complex.ofReal_one]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    have := sum_single_diag (n := n) (fun _ => (1 : ℂ))
    rw [this, Matrix.diagonal_one]
  · intro X
    have h : ∀ a : m × n,
        Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ) * X
          * (Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ))ᴴ
        = Matrix.single a.1 a.1 (((T a.1 a.2 : ℝ) : ℂ) * X a.2 a.2) := by
      rintro ⟨j, i⟩
      rw [single_conjTranspose, Matrix.single_mul_mul_single]
      congr 1
      have hsq : ((Real.sqrt (T j i) : ℝ) : ℂ) * ((Real.sqrt (T j i) : ℝ) : ℂ)
          = ((T j i : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hT j i)]
      rw [RCLike.star_def, Complex.conj_ofReal]
      calc ((Real.sqrt (T j i) : ℝ) : ℂ) * X i i * ((Real.sqrt (T j i) : ℝ) : ℂ)
          = (((Real.sqrt (T j i) : ℝ) : ℂ) * ((Real.sqrt (T j i) : ℝ) : ℂ)) * X i i := by ring
        _ = ((T j i : ℝ) : ℂ) * X i i := by rw [hsq]
    rw [Finset.sum_congr rfl (fun a _ => h a), Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun j _ => sum_single_const j _)]
    rw [sum_single_diag]
    rfl

/-- **Data processing for measure-and-prepare channels**: for an arbitrary faithful state `ρ`
and a faithful state `σ` which is diagonal in the measurement basis, the relative entropy does
not increase under the CPTP map `classicalChannel T`. -/
