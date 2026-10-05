/- (Lean requires `import` to be the first command, so this header is written as a plain
block comment; the module docstring `/-! ... -/` with the same content follows the imports.)
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix

namespace Chem

/-- Adjacency matrix of the cycle graph `C₄`: vertices are `Fin 4` (i.e. `ℤ/4ℤ`) and
`i` is adjacent to `j` exactly when `i - j = ±1` modulo `4`. -/
def C4adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/4)`, `k = 0,1,2,3`, are exactly `2, 0, -2`. -/
theorem range_two_cos : (Set.range fun k : Fin 4 => 2 * Real.cos (2 * Real.pi * k / 4))
    = ({2, 0, -2} : Set ℝ) := by
  have c1 : Real.cos (2 * Real.pi / 4) = 0 := by
    rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring]; exact Real.cos_pi_div_two
  have c2 : Real.cos (2 * Real.pi * 2 / 4) = -1 := by
    rw [show 2 * Real.pi * 2 / 4 = Real.pi by ring]; exact Real.cos_pi
  have c3 : Real.cos (2 * Real.pi * 3 / 4) = 0 := by
    rw [show 2 * Real.pi * 3 / 4 = Real.pi + Real.pi / 2 by ring, Real.cos_add]; simp
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num
    · right; left; norm_num [c1]
    · right; right; norm_num [c2]
    · right; left; norm_num [c3]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num [c1]⟩
    · exact ⟨2, by norm_num [c2]⟩

/-- **Hückel theory for cyclobutadiene (C₄).**  The eigenvalues of the adjacency matrix of the
cycle graph `C₄` are exactly the numbers `2 cos (2πk/4)` for `k = 0, 1, 2, 3`
(namely `2, 0, 0, -2`). -/
theorem huckel_C4 :
    {μ : ℝ | ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v}
      = Set.range fun k : Fin 4 => 2 * Real.cos (2 * Real.pi * k / 4) := by
  rw [range_two_cos]
  ext μ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    have e2 := congrFun h 2
    have e3 := congrFun h 3
    simp +decide [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
    -- `e0 : v 1 + v 3 = μ * v 0`, `e1 : v 0 + v 2 = μ * v 1`, etc.
    by_cases hμ : μ = 0
    · simp [hμ]
    · have hac : v 0 = v 2 := by
        have : μ * v 0 = μ * v 2 := by rw [← e0, ← e2]
        exact mul_left_cancel₀ hμ this
      have hbd : v 1 = v 3 := by
        have : μ * v 1 = μ * v 3 := by rw [← e1, ← e3]
        exact mul_left_cancel₀ hμ this
      have k0 : 2 * v 1 = μ * v 0 := by rw [← e0]; rw [hbd]; ring
      have k1 : 2 * v 0 = μ * v 1 := by rw [← e1]; rw [hac]; ring
      have hsq : (μ ^ 2 - 4) * v 0 = 0 := by linear_combination (-μ) * k0 + (-2) * k1
      have hne : v 0 ≠ 0 := by
        intro h0
        have h1 : v 1 = 0 := by
          have : μ * v 1 = 0 := by rw [← k1, h0]; ring
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hμ
          · exact h
        exact hv (funext fun i => by
          fin_cases i
          · exact h0
          · exact h1
          · exact hac ▸ h0
          · exact hbd ▸ h1)
      have : μ ^ 2 - 4 = 0 := by
        rcases mul_eq_zero.1 hsq with h | h
        · exact h
        · exact absurd h hne
      have hfac : (μ - 2) * (μ + 2) = 0 := by linear_combination this
      rcases mul_eq_zero.1 hfac with h | h
      · left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl)
    · refine ⟨![1, 1, 1, 1], ?_, ?_⟩
      · intro h; have := congrFun h 0; norm_num at this
      · funext i
        fin_cases i <;>
          simp +decide [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num
    · refine ⟨![1, 0, -1, 0], ?_, ?_⟩
      · intro h; have := congrFun h 0; norm_num at this
      · funext i
        fin_cases i <;>
          simp +decide [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · refine ⟨![1, -1, 1, -1], ?_, ?_⟩
      · intro h; have := congrFun h 0; norm_num at this
      · funext i
        fin_cases i <;>
          simp +decide [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

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

