import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PathSpectrum

/-- The 4-vertex path Hamiltonian: tridiagonal, 2 on the diagonal, -1 on each path edge.
    (Extends the verified H1, H2, H3 in the Constellation Spectrum.) -/

theorem H5_eigenvalue_center :
    H5.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly]
  have h : (Matrix.scalar (Fin 5) (2:ℝ)) - H5
      = !![0,1,0,0,0; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 0,0,0,1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H5]
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, Fin.lt_def, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

end BrockianFrontier.PathSpectrum

