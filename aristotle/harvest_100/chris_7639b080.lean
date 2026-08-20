/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header above is a plain block comment and is repeated as a doc comment below.)

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

/-! ### Values of `cos (2πm/4)` -/

/-- `cos (2πm/4)` only depends on `m % 4`. -/
theorem cos_quarter (m : ℕ) :
    Real.cos (2 * π * m / 4) = Real.cos (2 * π * ((m % 4 : ℕ) : ℝ) / 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4]
  rw [show (2 * π * (((4 * (m / 4) + m % 4 : ℕ)) : ℝ) / 4 : ℝ)
      = 2 * π * ((m % 4 : ℕ) : ℝ) / 4 + (m / 4 : ℕ) * (2 * π) by push_cast; ring]
  exact (Real.cos_periodic.nat_mul _) _

theorem cos_q0 : Real.cos (2 * π * ((0 : ℕ) : ℝ) / 4) = 1 := by norm_num

theorem cos_q1 : Real.cos (2 * π * ((1 : ℕ) : ℝ) / 4) = 0 := by
  rw [show (2 * π * ((1 : ℕ) : ℝ) / 4) = π / 2 by push_cast; ring, Real.cos_pi_div_two]

theorem cos_q2 : Real.cos (2 * π * ((2 : ℕ) : ℝ) / 4) = -1 := by
  rw [show (2 * π * ((2 : ℕ) : ℝ) / 4) = π by push_cast; ring, Real.cos_pi]

theorem cos_q3 : Real.cos (2 * π * ((3 : ℕ) : ℝ) / 4) = 0 := by
  rw [show (2 * π * ((3 : ℕ) : ℝ) / 4) = π / 2 + π by push_cast; ring, Real.cos_add_pi,
    Real.cos_pi_div_two, neg_zero]

theorem cosA : Real.cos (2 * π / 4) = 0 := by
  rw [show (2 * π / 4 : ℝ) = 2 * π * ((1 : ℕ) : ℝ) / 4 by push_cast; ring, cos_q1]

theorem cosB : Real.cos (2 * π * 2 / 4) = -1 := by
  rw [show (2 * π * 2 / 4 : ℝ) = 2 * π * ((2 : ℕ) : ℝ) / 4 by push_cast; ring, cos_q2]

theorem cosC : Real.cos (2 * π * 3 / 4) = 0 := by
  rw [show (2 * π * 3 / 4 : ℝ) = 2 * π * ((3 : ℕ) : ℝ) / 4 by push_cast; ring, cos_q3]

theorem cosD : Real.cos (2 * π * 2 * 2 / 4) = 1 := by
  rw [show (2 * π * 2 * 2 / 4 : ℝ) = 2 * π * ((4 : ℕ) : ℝ) / 4 by push_cast; ring, cos_quarter]
  norm_num [cos_q0]

theorem cosE : Real.cos (2 * π * 2 * 3 / 4) = -1 := by
  rw [show (2 * π * 2 * 3 / 4 : ℝ) = 2 * π * ((6 : ℕ) : ℝ) / 4 by push_cast; ring, cos_quarter]
  norm_num
  exact cosB

theorem cosF : Real.cos (2 * π * 3 * 2 / 4) = -1 := by
  rw [show (2 * π * 3 * 2 / 4 : ℝ) = 2 * π * ((6 : ℕ) : ℝ) / 4 by push_cast; ring, cos_quarter]
  norm_num
  exact cosB

theorem cosG : Real.cos (2 * π * 3 * 3 / 4) = 0 := by
  rw [show (2 * π * 3 * 3 / 4 : ℝ) = 2 * π * ((9 : ℕ) : ℝ) / 4 by push_cast; ring, cos_quarter]
  norm_num
  exact cosA

/-! ### The Hückel matrix of `C₄` -/

/-- Adjacency matrix of the cycle graph `C₄` on vertices `0,1,2,3`
(edges `0–1`, `1–2`, `2–3`, `3–0`).  In Hückel theory this matrix (with `α = 0`, `β = 1`)
governs the π-orbital energies of cyclobutadiene. -/
def A4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1;
     1, 0, 1, 0;
     0, 1, 0, 1;
     1, 0, 1, 0]

/-- The Hückel eigenvector attached to index `k`: `j ↦ cos (2πkj/4)`. -/
noncomputable def v4 (k : Fin 4) : Fin 4 → ℝ :=
  fun j => Real.cos (2 * π * (k : ℕ) * (j : ℕ) / 4)

theorem v4_zero : v4 0 = ![1, 1, 1, 1] := by
  funext j; fin_cases j <;> simp [v4]

theorem v4_one : v4 1 = ![1, 0, -1, 0] := by
  funext j; fin_cases j <;> simp [v4, cosA, cosB, cosC]

theorem v4_two : v4 2 = ![1, -1, 1, -1] := by
  funext j; fin_cases j <;> simp [v4, cosB, cosD, cosE]

theorem v4_three : v4 3 = ![1, 0, -1, 0] := by
  funext j; fin_cases j <;> simp [v4, cosC, cosF, cosG]

/-! ### The spectrum -/

/-- The characteristic polynomial of the `C₄` adjacency matrix, evaluated at any real `μ`,
factors as `∏ k, (μ - 2 cos (2πk/4))`. -/
theorem huckel_C4_charpoly (μ : ℝ) :
    (μ • (1 : Matrix (Fin 4) (Fin 4) ℝ) - A4).det
      = ∏ k : Fin 4, (μ - 2 * Real.cos (2 * π * (k : ℕ) / 4)) := by
  have hdet : (μ • (1 : Matrix (Fin 4) (Fin 4) ℝ) - A4).det = μ ^ 2 * (μ ^ 2 - 4) := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.one_apply, A4]
    norm_num [Fin.succAbove, Fin.lt_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE,
      Fin.ext_iff]
    ring
  rw [hdet, Fin.prod_univ_four]
  simp [cosA, cosB, cosC]
  ring

theorem eig_zero :
    A4.mulVec (v4 0) = (2 * Real.cos (2 * π * ((0 : Fin 4) : ℕ) / 4)) • v4 0 := by
  rw [v4_zero]
  funext j; fin_cases j <;>
    simp [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

theorem eig_one :
    A4.mulVec (v4 1) = (2 * Real.cos (2 * π * ((1 : Fin 4) : ℕ) / 4)) • v4 1 := by
  rw [v4_one]
  funext j; fin_cases j <;>
    simp [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, cosA]

theorem eig_two :
    A4.mulVec (v4 2) = (2 * Real.cos (2 * π * ((2 : Fin 4) : ℕ) / 4)) • v4 2 := by
  rw [v4_two]
  funext j; fin_cases j <;>
    simp [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, cosB] <;> norm_num

theorem eig_three :
    A4.mulVec (v4 3) = (2 * Real.cos (2 * π * ((3 : Fin 4) : ℕ) / 4)) • v4 3 := by
  rw [v4_three]
  funext j; fin_cases j <;>
    simp [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, cosC]

/-- For each `k`, the vector `j ↦ cos (2πkj/4)` is a nonzero eigenvector of the `C₄`
adjacency matrix with eigenvalue `2 cos (2πk/4)`. -/
theorem huckel_C4_eigenvector (k : Fin 4) :
    v4 k ≠ 0 ∧ A4.mulVec (v4 k) = (2 * Real.cos (2 * π * (k : ℕ) / 4)) • v4 k := by
  have h0 : v4 k 0 = 1 := by simp [v4]
  refine ⟨fun h => ?_, ?_⟩
  · rw [h] at h0; simp at h0
  · fin_cases k
    exacts [eig_zero, eig_one, eig_two, eig_three]

/-- **Hückel theory for cyclobutadiene (C₄).**  The adjacency eigenvalues of the cycle graph
`C₄` are exactly `2 cos (2πk/4)` for `k = 0,1,2,3`: the characteristic polynomial factors
accordingly, and each of these values carries an explicit nonzero eigenvector. -/
theorem huckel_C4 :
    (∀ μ : ℝ, (μ • (1 : Matrix (Fin 4) (Fin 4) ℝ) - A4).det
        = ∏ k : Fin 4, (μ - 2 * Real.cos (2 * π * (k : ℕ) / 4)))
      ∧ (∀ k : Fin 4, ∃ v : Fin 4 → ℝ, v ≠ 0 ∧
          A4.mulVec v = (2 * Real.cos (2 * π * (k : ℕ) / 4)) • v) :=
  ⟨huckel_C4_charpoly, fun k => ⟨v4 k, huckel_C4_eigenvector k⟩⟩

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

