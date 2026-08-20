/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem prod_ne_one {L : List (Fin 2 × Bool)} (hred : FreeGroup.IsReduced L) (hne : L ≠ []) :
    (L.map letterMat).prod ≠ 1 := by
  intro hone
  have h := prod_mulVec L
  rw [hone, Matrix.one_mulVec] at h
  have hsq : Real.sqrt 2 ≠ 0 := by positivity
  have hLv : vecR (0, 1, 0) 1 = Real.sqrt 2 := by norm_num [vecR]
  have hRv : ((((3 : ℝ)⁻¹) ^ L.length) • vecR (stateOf L)) 1
      = ((3 : ℝ)⁻¹) ^ L.length * (((stateOf L).2.1 : ℝ) * Real.sqrt 2) := by
    simp [vecR]
  have h1 : Real.sqrt 2 = ((3 : ℝ)⁻¹) ^ L.length * (((stateOf L).2.1 : ℝ) * Real.sqrt 2) :=
    calc Real.sqrt 2 = vecR (0, 1, 0) 1 := hLv.symm
      _ = ((((3 : ℝ)⁻¹) ^ L.length) • vecR (stateOf L)) 1 := by rw [h]
      _ = _ := hRv
  have h1' : (1 : ℝ) * Real.sqrt 2
      = (((3 : ℝ)⁻¹) ^ L.length * ((stateOf L).2.1 : ℝ)) * Real.sqrt 2 := by
    linear_combination h1
  have h2 : (1 : ℝ) = ((3 : ℝ)⁻¹) ^ L.length * ((stateOf L).2.1 : ℝ) :=
    mul_right_cancel₀ hsq h1'
  have h3 : ((stateOf L).2.1 : ℝ) = (3 : ℝ) ^ L.length := by
    rw [inv_pow] at h2
    field_simp at h2
    linarith [h2]
  have h4 : (stateOf L).2.1 = 3 ^ L.length := by
    have : ((stateOf L).2.1 : ℝ) = ((3 ^ L.length : ℤ) : ℝ) := by push_cast; exact h3
    exact_mod_cast this
  have hlen : L.length ≠ 0 := by simpa using hne
  have hdvd : (3 : ℤ) ∣ (stateOf L).2.1 := by
    rw [h4]
    exact dvd_pow_self 3 hlen
  exact (inv_of_isReduced L hred).1 hdvd

