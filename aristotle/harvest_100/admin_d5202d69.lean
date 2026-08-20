/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene
with `α = 0`, `β = 1`), viewed over `ℂ`. -/
def C4adj : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 1;
     1, 0, 1, 0;
     0, 1, 0, 1;
     1, 0, 1, 0]

/-- The predicted Hückel eigenvalues of `C₄`: `2 cos (2πk/4)`. -/
noncomputable def huckelEig (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 4)

lemma huckelEig_zero : huckelEig 0 = 2 := by
  simp [huckelEig]

lemma huckelEig_one : huckelEig 1 = 0 := by
  have h : 2 * Real.pi * ((1 : ℕ) : ℝ) / 4 = Real.pi / 2 := by push_cast; ring
  rw [huckelEig, h, Real.cos_pi_div_two, mul_zero]

lemma huckelEig_two : huckelEig 2 = -2 := by
  have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 4 = Real.pi := by push_cast; ring
  rw [huckelEig, h, Real.cos_pi]
  norm_num

lemma huckelEig_three : huckelEig 3 = 0 := by
  have h : 2 * Real.pi * ((3 : ℕ) : ℝ) / 4 = Real.pi / 2 + Real.pi := by push_cast; ring
  rw [huckelEig, h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

/-- The characteristic matrix of `C4adj`, written out explicitly. -/
lemma charmatrix_C4adj :
    charmatrix C4adj = !![X, -1, 0, -1; -1, X, -1, 0; 0, -1, X, -1; -1, 0, -1, X] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charmatrix, C4adj, Matrix.diagonal]

set_option maxRecDepth 10000 in
/-- The characteristic polynomial of the adjacency matrix of `C₄` is `X⁴ - 4X²`. -/
lemma charpoly_C4adj : C4adj.charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [Matrix.charpoly, charmatrix_C4adj]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **Hückel theory for cyclobutadiene (the cycle graph `C₄`).**

The eigenvalues of the adjacency matrix of `C₄` are exactly the numbers `2 cos (2πk/4)`
for `k = 0, 1, 2, 3`, and each of these numbers is indeed an eigenvalue, witnessed by an
explicit nonzero eigenvector. -/
theorem huckel_C4 :
    (∀ z : ℂ, z ∈ spectrum ℂ C4adj ↔ ∃ k : Fin 4, z = (huckelEig k.val : ℂ)) ∧
    (∀ k : Fin 4, ∃ v : Fin 4 → ℂ, v ≠ 0 ∧
      C4adj.mulVec v = (huckelEig k.val : ℂ) • v) := by
  constructor
  · intro z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, charpoly_C4adj]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    constructor
    · intro hz
      have h : z ^ 2 * ((z - 2) * (z + 2)) = 0 := by linear_combination hz
      rcases mul_eq_zero.1 h with h1 | h2
      · have hz0 : z = 0 := (pow_eq_zero_iff (two_ne_zero)).1 h1
        refine ⟨1, ?_⟩
        show z = ((huckelEig 1 : ℝ) : ℂ)
        rw [huckelEig_one, hz0, Complex.ofReal_zero]
      · rcases mul_eq_zero.1 h2 with h3 | h4
        · refine ⟨0, ?_⟩
          show z = ((huckelEig 0 : ℝ) : ℂ)
          rw [huckelEig_zero]
          push_cast
          linear_combination h3
        · refine ⟨2, ?_⟩
          show z = ((huckelEig 2 : ℝ) : ℂ)
          rw [huckelEig_two]
          push_cast
          linear_combination h4
    · rintro ⟨k, rfl⟩
      fin_cases k <;>
        norm_num [huckelEig_zero, huckelEig_one, huckelEig_two, huckelEig_three]
  · intro k
    fin_cases k
    · refine ⟨![1, 1, 1, 1], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · funext i
        fin_cases i <;>
          simp [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four, huckelEig_zero] <;>
          norm_num
    · refine ⟨![1, 0, -1, 0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · funext i
        fin_cases i <;>
          simp [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four, huckelEig_one]
    · refine ⟨![1, -1, 1, -1], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · funext i
        fin_cases i <;>
          simp [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four, huckelEig_two] <;>
          norm_num
    · refine ⟨![1, 0, -1, 0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · funext i
        fin_cases i <;>
          simp [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four, huckelEig_three]

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

