import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene,
with `α = 0`, `β = 1`): vertices are `Fin 4` arranged in a cycle, and `i ~ j` iff
`j = i + 1` or `i = j + 1` (addition modulo `4`). -/
def C4adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if j = i + 1 ∨ i = j + 1 then 1 else 0

theorem C4adj_eq : C4adj = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4adj]

/-- The characteristic determinant of `C4adj`. -/
theorem det_C4adj_sub (μ : ℝ) :
    (C4adj - μ • (1 : Matrix (Fin 4) (Fin 4) ℝ)).det = μ ^ 4 - 4 * μ ^ 2 := by
  have h : (C4adj - μ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
      = !![-μ, 1, 0, 1; 1, -μ, 1, 0; 0, 1, -μ, 1; 1, 0, 1, -μ] := by
    rw [C4adj_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Fin.castSucc, Fin.castAdd,
    Fin.castLE, Fin.succ]
  ring

/-- `μ` is an eigenvalue of `C4adj` iff the characteristic determinant vanishes. -/
theorem eigen_iff_det (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v) ↔ μ ^ 4 - 4 * μ ^ 2 = 0 := by
  rw [← det_C4adj_sub μ, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hve⟩
    exact ⟨v, hv, by simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hve]⟩
  · rintro ⟨v, hv, hvz⟩
    refine ⟨v, hv, ?_⟩
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hvz

/-- The four Hückel eigenvalues, as a set of real numbers. -/
theorem cos_values (μ : ℝ) :
    (∃ k : Fin 4, μ = 2 * Real.cos (2 * π * k / 4)) ↔ (μ = 2 ∨ μ = 0 ∨ μ = -2) := by
  have h0 : (2 : ℝ) * Real.cos (2 * π * ((0 : Fin 4) : ℕ) / 4) = 2 := by norm_num
  have h1 : (2 : ℝ) * Real.cos (2 * π * ((1 : Fin 4) : ℕ) / 4) = 0 := by
    have h : (2 : ℝ) * π * ((1 : Fin 4) : ℕ) / 4 = π / 2 := by norm_num; ring
    rw [h, Real.cos_pi_div_two, mul_zero]
  have h2 : (2 : ℝ) * Real.cos (2 * π * ((2 : Fin 4) : ℕ) / 4) = -2 := by
    have h : (2 : ℝ) * π * ((2 : Fin 4) : ℕ) / 4 = π := by norm_num; ring
    rw [h, Real.cos_pi]; norm_num
  have h3 : (2 : ℝ) * Real.cos (2 * π * ((3 : Fin 4) : ℕ) / 4) = 0 := by
    have h : (2 : ℝ) * π * ((3 : Fin 4) : ℕ) / 4 = π + π / 2 := by norm_num; ring
    rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
    ring
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h3)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
    · exact ⟨2, h2.symm⟩

/-- **Hückel theory for cyclobutadiene (`C₄`).**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₄`
(i.e. `C4adj *ᵥ v = μ • v` for some nonzero `v`) if and only if
`μ = 2 * cos (2 * π * k / 4)` for some `k ∈ {0, 1, 2, 3}`. -/
theorem huckel_C4 (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 4, μ = 2 * Real.cos (2 * π * k / 4) := by
  rw [eigen_iff_det, cos_values]
  constructor
  · intro h
    have h' : μ ^ 2 * ((μ - 2) * (μ + 2)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inr (Or.inl (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1))
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

