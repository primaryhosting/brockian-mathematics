/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
with `α = 0`, `β = 1`). -/
def adjC3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 1; 1, 0, 1; 1, 1, 0]

/-- The characteristic determinant of `C₃`: `det (μ I - A) = (μ - 2) (μ + 1)²`. -/
lemma det_smul_one_sub_adjC3 (μ : ℝ) :
    (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3).det = (μ - 2) * (μ + 1) ^ 2 := by
  have h : (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3) =
      !![μ, -1, -1; -1, μ, -1; -1, -1, μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjC3]
  rw [h, Matrix.det_fin_three]
  simp
  ring

/-- The three values `2 cos (2πk/3)`, `k = 0, 1, 2`, are exactly `2`, `-1`, `-1`. -/
lemma two_cos_values (k : Fin 3) :
    2 * Real.cos (2 * π * (k : ℕ) / 3) = if k = 0 then 2 else -1 := by
  fin_cases k
  · norm_num
  · rw [show (2 * π * ((1 : ℕ) : ℝ) / 3) = π - π / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · rw [show (2 * π * ((2 : ℕ) : ℝ) / 3) = π + π / 3 by push_cast; ring, Real.cos_add]
    simp [Real.cos_pi_div_three]

/-- **Hückel theory for `C₃`.**  A real number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₃` (i.e. there is a nonzero vector `v` with `A v = μ v`)
if and only if `μ = 2 cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
theorem huckel_C3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ adjC3.mulVec v = μ • v) ↔
      ∃ k : Fin 3, μ = 2 * Real.cos (2 * π * (k : ℕ) / 3) := by
  have hrw : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ adjC3.mulVec v = μ • v) ↔
      ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3).mulVec v = 0 := by
    constructor
    · rintro ⟨v, hv, hA⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    · rintro ⟨v, hv, hA⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hA
      exact hA.symm
  rw [hrw, Matrix.exists_mulVec_eq_zero_iff, det_smul_one_sub_adjC3]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h2
    · refine ⟨0, ?_⟩
      rw [two_cos_values]
      simpa using (sub_eq_zero.1 h1)
    · have hμ : μ + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
      refine ⟨1, ?_⟩
      rw [two_cos_values]
      norm_num
      linarith
  · rintro ⟨k, rfl⟩
    rw [two_cos_values]
    fin_cases k <;> norm_num

/-- Explicit eigenvectors for `C₃`: the constant vector for the eigenvalue `2`, and two
independent vectors for the doubly degenerate eigenvalue `-1`. -/
theorem huckel_C3_eigenvectors :
    adjC3.mulVec ![1, 1, 1] = (2 : ℝ) • ![1, 1, 1] ∧
    adjC3.mulVec ![1, -1, 0] = (-1 : ℝ) • ![1, -1, 0] ∧
    adjC3.mulVec ![0, 1, -1] = (-1 : ℝ) • ![0, 1, -1] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext i
      fin_cases i <;>
        simp [adjC3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- Spectrum form of the Hückel result for `C₃`: the spectrum of the adjacency matrix is
exactly the set of Hückel eigenvalues `2 cos (2πk/3)`, `k = 0, 1, 2`. -/
theorem huckel_C3_spectrum :
    spectrum ℝ adjC3 = {μ : ℝ | ∃ k : Fin 3, μ = 2 * Real.cos (2 * π * (k : ℕ) / 3)} := by
  ext μ
  have hspec : μ ∈ spectrum ℝ adjC3 ↔
      (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3).det = 0 := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
    simp [Algebra.algebraMap_eq_smul_one, isUnit_iff_ne_zero]
  rw [hspec, Set.mem_setOf_eq, ← Matrix.exists_mulVec_eq_zero_iff]
  rw [← huckel_C3 μ]
  constructor
  · rintro ⟨v, hv, hA⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hA
    exact hA.symm
  · rintro ⟨v, hv, hA⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

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

