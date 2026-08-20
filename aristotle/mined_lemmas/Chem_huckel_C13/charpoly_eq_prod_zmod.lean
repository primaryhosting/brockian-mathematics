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

set_option grind.warning false

namespace Chem

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

lemma charpoly_eq_prod_zmod :
    adjC13.charpoly = ∏ k : ZMod 13, (X - C (eval13 k)) := by
  obtain ⟨u, hu⟩ := isUnit_fmat
  have key := adj_mul_fmat
  rw [← hu] at key
  have hA : adjC13
      = u.val * Matrix.diagonal eval13 * (u⁻¹ : (Matrix (ZMod 13) (ZMod 13) ℂ)ˣ).val := by
    calc adjC13 = adjC13 * (u.val * (u⁻¹ : (Matrix (ZMod 13) (ZMod 13) ℂ)ˣ).val) := by simp
      _ = (adjC13 * u.val) * (u⁻¹ : (Matrix (ZMod 13) (ZMod 13) ℂ)ˣ).val := by rw [mul_assoc]
      _ = _ := by rw [key]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel theory for the cycle `C₁₃`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₃` is `∏_{k=0}^{12} (X - 2 cos (2πk/13))`; i.e. the adjacency
eigenvalues of `C₁₃` are exactly the numbers `2 cos (2πk/13)`, `k = 0, …, 12`. -/
