import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma C17adj_mul_U17 : C17adj * U17 = U17 * D17 := by
  ext i k
  have hleft : (C17adj * U17) i k = U17 (i + 1) k + U17 (i - 1) k := by
    rw [Matrix.mul_apply]
    have hterm : ∀ j : ZMod 17, C17adj i j * U17 j k =
        if j ∈ ({i + 1, i - 1} : Finset (ZMod 17)) then U17 j k else 0 := by
      intro j
      by_cases h : j = i + 1 ∨ j = i - 1
      · simp [C17adj, h, Finset.mem_insert, Finset.mem_singleton]
      · simp only [C17adj, if_neg h]
        rw [if_neg (by simpa [Finset.mem_insert, Finset.mem_singleton] using h)]
        ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_pair (succ_ne_pred i)]
  have hright : (U17 * D17) i k = U17 i k * (ee k + ee (-k)) := by
    rw [Matrix.mul_apply]
    simp [D17, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [hleft, hright]
  simp only [U17]
  rw [mul_add, ← ee_add, ← ee_add]
  congr 2 <;> ring

/-- The diagonal entries are the Hückel eigenvalues `2 cos (2πk/17)`. -/
