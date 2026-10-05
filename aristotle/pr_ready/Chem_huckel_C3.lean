/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Statement: The adjacency eigenvalues of the cycle graph C_3 are 2·cos(2πk/3) for k=0..2.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real

namespace Chem

/-- Adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices is adjacent. -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

lemma C3adj_mulVec (v : Fin 3 → ℝ) (i : Fin 3) :
    C3adj.mulVec v i = (v 0 + v 1 + v 2) - v i := by
  fin_cases i <;>
    simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

lemma two_cos_zero : 2 * Real.cos (2 * π * (0 : ℕ) / 3) = 2 := by
  norm_num

lemma two_cos_one : 2 * Real.cos (2 * π * (1 : ℕ) / 3) = -1 := by
  have h : 2 * π * ((1 : ℕ) : ℝ) / 3 = π - π / 3 := by push_cast; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma two_cos_two : 2 * Real.cos (2 * π * (2 : ℕ) / 3) = -1 := by
  have h : 2 * π * ((2 : ℕ) : ℝ) / 3 = 2 * π - (π - π / 3) := by push_cast; ring
  rw [h, Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- **Hückel theory for `C₃`.**  A real number `μ` is an eigenvalue of the adjacency matrix of
the cycle graph `C₃` (i.e. it admits a nonzero eigenvector) if and only if it is of the form
`2 * cos (2 π k / 3)` for some `k ∈ {0, 1, 2}`.  (The eigenvalues are `2, -1, -1`.) -/
theorem huckel_C3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 3 ∧ μ = 2 * Real.cos (2 * π * k / 3) := by
  constructor
  · rintro ⟨v, hv, hEq⟩
    have h : ∀ i, (v 0 + v 1 + v 2) - v i = μ * v i := by
      intro i
      have := congrFun hEq i
      rwa [C3adj_mulVec, Pi.smul_apply, smul_eq_mul] at this
    have key : ∀ i, (μ + 1) * v i = v 0 + v 1 + v 2 := by
      intro i; linear_combination -(h i)
    by_cases hμ : μ = -1
    · exact ⟨1, by norm_num, by rw [two_cos_one, hμ]⟩
    · have hne : μ + 1 ≠ 0 := fun hc => hμ (by linarith)
      have h01 : v 0 = v 1 := mul_left_cancel₀ hne (by rw [key 0, key 1])
      have h02 : v 0 = v 2 := mul_left_cancel₀ hne (by rw [key 0, key 2])
      have hv0 : v 0 ≠ 0 := by
        intro hc
        apply hv
        have h1 : v 1 = 0 := by rw [← h01]; exact hc
        have h2 : v 2 = 0 := by rw [← h02]; exact hc
        funext i
        fin_cases i <;> simp [hc, h1, h2]
      have hμ2 : μ = 2 := by
        have h0 := key 0
        rw [← h01, ← h02] at h0
        have hz : (μ - 2) * v 0 = 0 := by linear_combination h0
        rcases mul_eq_zero.mp hz with hz | hz
        · linarith
        · exact absurd hz hv0
      exact ⟨0, by norm_num, by rw [two_cos_zero, hμ2]⟩
  · rintro ⟨k, hk3, hk⟩
    have hcases : μ = 2 ∨ μ = -1 := by
      interval_cases k
      · rw [two_cos_zero] at hk; exact Or.inl hk
      · rw [two_cos_one] at hk; exact Or.inr hk
      · rw [two_cos_two] at hk; exact Or.inr hk
    rcases hcases with hμ | hμ
    · refine ⟨fun _ => 1, ?_, ?_⟩
      · intro hc
        have := congrFun hc 0
        norm_num at this
      · funext i
        rw [C3adj_mulVec, hμ]
        norm_num
    · refine ⟨![1, -1, 0], ?_, ?_⟩
      · intro hc
        have := congrFun hc 0
        norm_num at this
      · funext i
        rw [C3adj_mulVec, hμ]
        fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.tail_cons]

end Chem


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

