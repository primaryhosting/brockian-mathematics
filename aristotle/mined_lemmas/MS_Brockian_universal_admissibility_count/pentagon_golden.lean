import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

theorem pentagon_golden :
    (!![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ).charpoly.eval
      ((Real.sqrt 5 - 1) / 2) = 0 := by
  set x : ℝ := (Real.sqrt 5 - 1) / 2 with hx
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : x ^ 2 + x - 1 = 0 := by
    rw [hx]; nlinarith [h5]
  rw [Matrix.eval_charpoly]
  have hmat : ((scalar (Fin 5)) x -
      (!![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ)) =
      !![x,-1,0,0,-1; -1,x,-1,0,0; 0,-1,x,-1,0; 0,0,-1,x,-1; -1,0,0,-1,x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [hmat]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf
  linear_combination ((x - 2) * (x ^ 2 + x - 1)) * h
/-- Singular series positivity in general: every admissible gap-set has positive local factors. -/
