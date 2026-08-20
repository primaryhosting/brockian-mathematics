import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem H_conj_Y : H * PY * Hᴴ = -PY := by
  have hcs : hc ^ 2 = 1 / 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hc, inv_pow, ← Complex.ofReal_pow, h2]
    norm_num
  have hconj : (starRingEnd ℂ) hc = hc := by rw [hc]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, H, PY, Matrix.conjTranspose_apply, hconj] <;>
    ring_nf
  all_goals simp only [hcs]
  all_goals ring_nf

