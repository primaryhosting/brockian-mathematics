import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₄` (vertices indexed cyclically by `Fin 4`:
`i` is adjacent to `i + 1` and `i - 1`). -/
def C4adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- Explicit description of the action of the `C₄` adjacency matrix on a vector. -/
lemma C4adj_mulVec (v : Fin 4 → ℝ) :
    C4adj *ᵥ v = ![v 1 + v 3, v 0 + v 2, v 1 + v 3, v 0 + v 2] := by
  funext i
  fin_cases i <;>
    simp +decide [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The four Hückel expressions `2·cos(2πk/4)`, `k = 0, 1, 2, 3`, are `2, 0, -2, 0`. -/
lemma two_cos_two_pi_k_div_four (k : Fin 4) :
    2 * Real.cos (2 * Real.pi * k / 4) = ![2, 0, -2, 0] k := by
  fin_cases k
  · norm_num
  · norm_num [show 2 * Real.pi / 4 = Real.pi / 2 by ring]
  · norm_num [show 2 * Real.pi * 2 / 4 = Real.pi by ring]
  · norm_num [show 2 * Real.pi * 3 / 4 = Real.pi + Real.pi / 2 by ring, Real.cos_add]

/-- **Hückel theory for cyclobutadiene (C₄).**  A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₄` if and only if `μ = 2·cos(2πk/4)` for some
`k ∈ {0, 1, 2, 3}` (i.e. `μ ∈ {2, 0, -2}`, the Hückel π-levels `α + 2β, α, α, α - 2β`). -/
theorem huckel_C4 (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 4, μ = 2 * Real.cos (2 * Real.pi * k / 4) := by
  constructor
  · rintro ⟨v, hv, h⟩
    rw [C4adj_mulVec] at h
    have e0 : v 1 + v 3 = μ * v 0 := by simpa using congrFun h 0
    have e1 : v 0 + v 2 = μ * v 1 := by simpa using congrFun h 1
    have e2 : v 1 + v 3 = μ * v 2 := by simpa using congrFun h 2
    have e3 : v 0 + v 2 = μ * v 3 := by simpa using congrFun h 3
    have key : μ = 2 ∨ μ = 0 ∨ μ = -2 := by
      by_cases hμ : μ = 0
      · exact Or.inr (Or.inl hμ)
      · have h02 : v 0 = v 2 := mul_left_cancel₀ hμ (by rw [← e0, ← e2])
        have h13 : v 1 = v 3 := mul_left_cancel₀ hμ (by rw [← e1, ← e3])
        have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
          by_contra hc
          push_neg at hc
          refine hv (funext fun i => ?_)
          fin_cases i <;> simp [hc.1, hc.2, ← h02, ← h13]
        have hsq : (μ - 2) * (μ + 2) = 0 := by
          rcases hne with h0 | h1
          · have hz : (μ * μ - 4) * v 0 = 0 := by
              linear_combination (-μ) * e0 - 2 * e1 - 2 * h02 - μ * h13
            rcases mul_eq_zero.1 hz with h' | h'
            · linear_combination h'
            · exact absurd h' h0
          · have hz : (μ * μ - 4) * v 1 = 0 := by
              linear_combination (-2) * e0 - μ * e1 - μ * h02 - 2 * h13
            rcases mul_eq_zero.1 hz with h' | h'
            · linear_combination h'
            · exact absurd h' h1
        rcases mul_eq_zero.1 hsq with h' | h'
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inr (by linarith))
    rcases key with h' | h' | h'
    · exact ⟨0, by rw [two_cos_two_pi_k_div_four]; simpa using h'⟩
    · exact ⟨1, by rw [two_cos_two_pi_k_div_four]; simpa using h'⟩
    · exact ⟨2, by rw [two_cos_two_pi_k_div_four]; simpa using h'⟩
  · rintro ⟨k, hk⟩
    rw [two_cos_two_pi_k_div_four] at hk
    have main : ∀ w : Fin 4 → ℝ, w 0 ≠ 0 → C4adj *ᵥ w = μ • w →
        ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v :=
      fun w hw h => ⟨w, fun hc => hw (by rw [hc]; rfl), h⟩
    fin_cases k <;> simp [Matrix.cons_val] at hk <;> subst hk
    · exact main ![1, 1, 1, 1] (by norm_num) (by
        rw [C4adj_mulVec]; funext i; fin_cases i <;> simp [Matrix.cons_val] <;> norm_num)
    · exact main ![1, 0, -1, 0] (by norm_num) (by
        rw [C4adj_mulVec]; funext i; fin_cases i <;> simp [Matrix.cons_val])
    · exact main ![1, -1, 1, -1] (by norm_num) (by
        rw [C4adj_mulVec]; funext i; fin_cases i <;> simp [Matrix.cons_val] <;> norm_num)
    · exact main ![1, 0, -1, 0] (by norm_num) (by
        rw [C4adj_mulVec]; funext i; fin_cases i <;> simp [Matrix.cons_val])

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

