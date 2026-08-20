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

theorem relEntropy_nonneg {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    0 ≤ relEntropy ρ σ := by
  obtain ⟨hρpd, hρtr⟩ := hρ
  obtain ⟨hσpd, hσtr⟩ := hσ
  have hρh : ρ.IsHermitian := hρpd.1
  have hσh : σ.IsHermitian := hσpd.1
  have hrsum : ∑ i, hρh.eigenvalues i = 1 := by
    have h1 := hρh.trace_eq_sum_eigenvalues
    rw [hρtr] at h1
    have h2 : ((∑ i, hρh.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  have hssum : ∑ i, hσh.eigenvalues i = 1 := by
    have h1 := hσh.trace_eq_sum_eigenvalues
    rw [hσtr] at h1
    have h2 : ((∑ i, hσh.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  have hkey := sum_mul_log_le
    (r := hρh.eigenvalues) (s := hσh.eigenvalues)
    (P := fun i j => Complex.normSq ((star (hρh.eigenvectorUnitary : Matrix n n ℂ)
      * (hσh.eigenvectorUnitary : Matrix n n ℂ)) i j))
    (fun i j => Complex.normSq_nonneg _)
    (fun i => normSq_row_sum _ (mul_star_conj_unitary _ _) i)
    (fun j => normSq_col_sum _ (star_mul_conj_unitary _ _) j)
    (fun i => hρpd.eigenvalues_pos i) (fun j => hσpd.eigenvalues_pos j) hrsum hssum
  rw [relEntropy, trace_mul_logM_self_re hρh, trace_mul_logM_re hρh hσh, sub_nonneg]
  refine le_trans (le_of_eq ?_) hkey
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Unitary invariance -/

