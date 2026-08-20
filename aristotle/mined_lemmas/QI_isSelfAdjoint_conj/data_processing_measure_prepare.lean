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

theorem data_processing_measure_prepare {m : Type u} [Fintype m] [DecidableEq m] {T : m → n → ℝ}
    (hT : ∀ j i, 0 ≤ T j i) (hTcol : ∀ i, ∑ j, T j i = 1) (hTrow : ∀ j, ∃ i, 0 < T j i)
    {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) (hdiag : dephase σ = σ) :
    relEntropy (classicalChannel T ρ) (classicalChannel T σ) ≤ relEntropy ρ σ := by
  set p : n → ℝ := fun i => (ρ i i).re with hpdef
  set q : n → ℝ := fun i => (σ i i).re with hqdef
  have hp : ∀ i, 0 < p i := fun i => (posDef_diag_re hρ.1 i).1
  have hq : ∀ i, 0 < q i := fun i => (posDef_diag_re hσ.1 i).1
  have hρe : ∀ i, ρ i i = ((p i : ℝ) : ℂ) := fun i => (posDef_diag_re hρ.1 i).2
  have hσe : ∀ i, σ i i = ((q i : ℝ) : ℂ) := fun i => (posDef_diag_re hσ.1 i).2
  have hTp : ∀ j, 0 < ∑ i, T j i * p i := by
    intro j
    obtain ⟨i, hi⟩ := hTrow j
    calc (0 : ℝ) < T j i * p i := mul_pos hi (hp i)
      _ ≤ ∑ i, T j i * p i :=
        Finset.single_le_sum (f := fun i => T j i * p i)
          (fun i _ => mul_nonneg (hT j i) (hp i).le) (Finset.mem_univ i)
  have hTq : ∀ j, 0 < ∑ i, T j i * q i := by
    intro j
    obtain ⟨i, hi⟩ := hTrow j
    calc (0 : ℝ) < T j i * q i := mul_pos hi (hq i)
      _ ≤ ∑ i, T j i * q i :=
        Finset.single_le_sum (f := fun i => T j i * q i)
          (fun i _ => mul_nonneg (hT j i) (hq i).le) (Finset.mem_univ i)
  have hch : ∀ (τ : Matrix n n ℂ) (r : n → ℝ), (∀ i, τ i i = ((r i : ℝ) : ℂ)) →
      classicalChannel T τ = Matrix.diagonal (fun j => (((∑ i, T j i * r i : ℝ)) : ℂ)) := by
    intro τ r hτ
    rw [classicalChannel]
    congr 1
    funext j
    rw [show ((∑ i, T j i * r i : ℝ) : ℂ) = ∑ i, ((T j i * r i : ℝ) : ℂ) from
      Complex.ofReal_sum _ _]
    exact Finset.sum_congr rfl fun i _ => by rw [hτ i, ← Complex.ofReal_mul]
  have hdeρ : dephase ρ = Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) := by
    rw [dephase]
    congr 1
    funext i
    exact hρe i
  have hdeσ : dephase σ = Matrix.diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    rw [dephase]
    congr 1
    funext i
    exact hσe i
  calc relEntropy (classicalChannel T ρ) (classicalChannel T σ)
      = ∑ j, (∑ i, T j i * p i) *
          (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i)) := by
        rw [hch ρ p hρe, hch σ q hσe, relEntropy_diagonal]
    _ ≤ ∑ i, p i * (Real.log (p i) - Real.log (q i)) :=
        classical_dpi hT hTcol hp hq hTp hTq
    _ = relEntropy (dephase ρ) (dephase σ) := by rw [hdeρ, hdeσ, relEntropy_diagonal]
    _ ≤ relEntropy ρ σ := data_processing_dephasing hρ hσ hdiag

/-! ### Measurement in an arbitrary orthonormal basis -/

