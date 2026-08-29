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

/-- The adjacency matrix of the cycle graph `C₃` (the complete graph on 3 vertices):
zero on the diagonal, one off the diagonal. -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  have h : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

lemma cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  have h : (4 : ℝ) * Real.pi / 3 = 2 * Real.pi - 2 * Real.pi / 3 := by ring
  rw [h, Real.cos_two_pi_sub, cos_two_pi_div_three]

/-- The three Hückel eigenvalues `2 cos(2πk/3)` are `2, -1, -1`. -/
lemma huckel_C3_values (k : Fin 3) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) = if k = 0 then 2 else -1 := by
  fin_cases k
  · norm_num
  · norm_num
    rw [cos_two_pi_div_three]
    norm_num
  · norm_num
    rw [show (2 : ℝ) * Real.pi * 2 / 3 = 4 * Real.pi / 3 by ring, cos_four_pi_div_three]
    norm_num

/-- **Hückel theory for `C₃`.** A real number `μ` is an eigenvalue of the adjacency matrix of
the cycle graph `C₃` if and only if it is of the form `2 cos(2πk/3)` for some `k = 0, 1, 2`. -/
theorem huckel_C3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  have key : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔ (μ = 2 ∨ μ = -1) := by
    constructor
    · rintro ⟨v, hv, h⟩
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
      by_cases hμ : μ = 2
      · exact Or.inl hμ
      · right
        have hS : v 0 + v 1 + v 2 = 0 := by
          have : (μ - 2) * (v 0 + v 1 + v 2) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact absurd (by linarith : μ = 2) hμ
          · exact h
        have e0 : (μ + 1) * v 0 = 0 := by linarith
        have e1 : (μ + 1) * v 1 = 0 := by linarith
        have e2 : (μ + 1) * v 2 = 0 := by linarith
        by_contra hne
        have hμ1 : μ + 1 ≠ 0 := fun hc => hne (by linarith)
        apply hv
        funext i
        fin_cases i
        · simpa using (mul_eq_zero.1 e0).resolve_left hμ1
        · simpa using (mul_eq_zero.1 e1).resolve_left hμ1
        · simpa using (mul_eq_zero.1 e2).resolve_left hμ1
    · rintro (rfl | rfl)
      · refine ⟨fun _ => 1, ?_, ?_⟩
        · intro hc
          have := congrFun hc 0
          norm_num at this
        · funext i
          fin_cases i <;>
            simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
      · refine ⟨fun i => if i = 0 then 1 else if i = 1 then -1 else 0, ?_, ?_⟩
        · intro hc
          have := congrFun hc 0
          norm_num at this
        · funext i
          fin_cases i <;>
            simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [key]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [huckel_C3_values]; norm_num⟩
  · rintro ⟨k, rfl⟩
    rw [huckel_C3_values]
    by_cases hk : k = 0 <;> simp [hk]

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

