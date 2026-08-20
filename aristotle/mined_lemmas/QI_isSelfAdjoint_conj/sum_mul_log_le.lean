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

theorem sum_mul_log_le {r s : n → ℝ} {P : n → n → ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) (hcol : ∀ j, ∑ i, P i j = 1)
    (hr : ∀ i, 0 < r i) (hs : ∀ j, 0 < s j) (hrsum : ∑ i, r i = 1) (hssum : ∑ j, s j = 1) :
    ∑ i, ∑ j, r i * P i j * Real.log (s j) ≤ ∑ i, r i * Real.log (r i) := by
  set t : n → ℝ := fun i => ∑ j, P i j * s j with ht
  have htpos : ∀ i, 0 < t i := by
    intro i
    have hex : ∃ j, 0 < P i j := by
      by_contra h
      push_neg at h
      have hz : ∑ j, P i j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hP i j)
      rw [hrow i] at hz
      norm_num at hz
    obtain ⟨j, hj⟩ := hex
    calc (0 : ℝ) < P i j * s j := mul_pos hj (hs j)
      _ ≤ ∑ j, P i j * s j :=
        Finset.single_le_sum (f := fun j => P i j * s j)
          (fun j _ => mul_nonneg (hP i j) (hs j).le) (Finset.mem_univ j)
  have hA : ∀ i, ∑ j, P i j * Real.log (s j) ≤ Real.log (t i) := by
    intro i
    have key : ∀ j ∈ Finset.univ, P i j * Real.log (s j) - P i j * Real.log (t i)
        ≤ P i j * (s j / t i - 1) := by
      intro j _
      have h1 : Real.log (s j / t i) ≤ s j / t i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hs j) (htpos i))
      have h2 : Real.log (s j / t i) = Real.log (s j) - Real.log (t i) :=
        Real.log_div (ne_of_gt (hs j)) (ne_of_gt (htpos i))
      rw [h2] at h1
      nlinarith [hP i j]
    have hsum := Finset.sum_le_sum key
    have hL : ∑ j, (P i j * Real.log (s j) - P i j * Real.log (t i))
        = (∑ j, P i j * Real.log (s j)) - Real.log (t i) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow i, one_mul]
    have hR : ∑ j, P i j * (s j / t i - 1) = 0 := by
      have h : ∑ j, P i j * (s j / t i - 1) = (∑ j, P i j * s j) / t i - ∑ j, P i j := by
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
      have h2 : (∑ j, P i j * s j) = t i := by rw [ht]
      rw [h, h2, hrow i, div_self (htpos i).ne', sub_self]
    rw [hL, hR] at hsum
    linarith
  have hB : ∑ i, r i * Real.log (t i) ≤ ∑ i, r i * Real.log (r i) := by
    have htsum : ∑ i, t i = 1 := by
      simp only [ht]
      rw [Finset.sum_comm]
      calc ∑ j, ∑ i, P i j * s j = ∑ j, (∑ i, P i j) * s j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
        _ = 1 := by simp [hcol, hssum]
    have key : ∀ i ∈ Finset.univ, r i * Real.log (t i) - r i * Real.log (r i) ≤ t i - r i := by
      intro i _
      have h1 : Real.log (t i / r i) ≤ t i / r i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (htpos i) (hr i))
      have h2 : Real.log (t i / r i) = Real.log (t i) - Real.log (r i) :=
        Real.log_div (ne_of_gt (htpos i)) (ne_of_gt (hr i))
      rw [h2] at h1
      have hri := hr i
      have h3 : r i * (Real.log (t i) - Real.log (r i)) ≤ r i * (t i / r i - 1) :=
        mul_le_mul_of_nonneg_left h1 hri.le
      have hrr : r i * (t i / r i - 1) = t i - r i := by field_simp
      nlinarith
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htsum, hrsum] at hsum
    linarith
  calc ∑ i, ∑ j, r i * P i j * Real.log (s j)
      = ∑ i, r i * (∑ j, P i j * Real.log (s j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, r i * Real.log (t i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA i) (hr i).le
    _ ≤ ∑ i, r i * Real.log (r i) := hB

/-! ### Spectral computations of the relative entropy -/

