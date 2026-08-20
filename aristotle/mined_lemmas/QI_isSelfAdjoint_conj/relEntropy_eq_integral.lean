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

theorem relEntropy_eq_integral {P Q : Matrix n n ℂ} (hP : IsDensity P) (hQ : IsDensity Q) :
    relEntropy P Q = ∫ t in Set.Ioi (0 : ℝ), chi t hP.1.1 hQ.1.1 / (1 + t) ^ 2 := by
  obtain ⟨hPd, hPtr⟩ := hP
  obtain ⟨hQd, hQtr⟩ := hQ
  set p := hPd.1.eigenvalues with hp
  set q := hQd.1.eigenvalues with hq
  set w : n → n → ℝ := fun j k => Complex.normSq ((star (hPd.1.eigenvectorUnitary
    : Matrix n n ℂ) * (hQd.1.eigenvectorUnitary : Matrix n n ℂ)) j k) with hw
  have hrow : ∀ j, ∑ k, w j k = 1 := fun j =>
    normSq_row_sum _ (mul_star_conj_unitary _ _) j
  have hcol : ∀ k, ∑ j, w j k = 1 := fun k =>
    normSq_col_sum _ (star_mul_conj_unitary _ _) k
  have hpsum : ∑ j, p j = 1 := by
    have h1 := hPd.1.trace_eq_sum_eigenvalues
    rw [hPtr] at h1
    have h2 : ((∑ j, p j : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  have hqsum : ∑ k, q k = 1 := by
    have h1 := hQd.1.trace_eq_sum_eigenvalues
    rw [hQtr] at h1
    have h2 : ((∑ k, q k : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  rw [integral_chi_eq hPd hQd]
  have hsplit : ∀ j k, w j k * (p j * Real.log (p j) - p j * Real.log (q k) - p j + q k)
      = w j k * (p j * Real.log (p j)) - w j k * (p j * Real.log (q k))
        - w j k * p j + w j k * q k := by
    intro j k
    ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hsplit j k]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have e1 : ∑ j, (∑ k, w j k) * (p j * Real.log (p j)) = ∑ j, p j * Real.log (p j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrow j, one_mul]
  have e3 : ∑ j, (∑ k, w j k) * p j = 1 := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hrow j, one_mul]]
    exact hpsum
  have e4 : ∑ j, ∑ k, w j k * q k = 1 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_mul, hcol k, one_mul]]
    exact hqsum
  rw [relEntropy, trace_mul_logM_self_re hPd.1, trace_mul_logM_re hPd.1 hQd.1]
  rw [e1, e3, e4]
  have e2 : ∑ j, ∑ k, p j * Real.log (q k) * w j k
      = ∑ j, ∑ k, w j k * (p j * Real.log (q k)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e2]
  ring

/-! ### The data processing inequality -/

/-- **Data processing inequality**: the Umegaki relative entropy of two faithful states does not
increase under a CPTP map (provided the output states are again faithful). -/
