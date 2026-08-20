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

theorem rZ_nat_smul_cVec_ne (n : ℕ) (hn : 1 ≤ n) : (rZ (n : ℝ)) • cVec ≠ cVec := by
  intro hc
  have hoff : cVec 0 ≠ 0 ∨ cVec 1 ≠ 0 := Or.inl (by rw [cVec_zero]; norm_num)
  obtain ⟨hcos, -⟩ := rZ_fix (n : ℝ) cVec hoff hc
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (n : ℝ)).mp hcos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    linarith [hk ▸ hnpos]
  have hpi : Real.pi = (n : ℝ) / (2 * k) := by
    have h2k : (2 * (k : ℝ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast hk0
    field_simp
    linarith [hk]
  have hirr : Irrational ((((n : ℚ) / (2 * (k : ℚ))) : ℚ) : ℝ) := by
    rw [show ((((n : ℚ) / (2 * (k : ℚ))) : ℚ) : ℝ) = (n : ℝ) / (2 * (k : ℝ)) by push_cast; ring,
      ← hpi]
    exact irrational_pi
  exact (Rat.not_irrational _) hirr

