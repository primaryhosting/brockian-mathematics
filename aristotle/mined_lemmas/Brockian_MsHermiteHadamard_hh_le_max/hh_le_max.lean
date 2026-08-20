import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_le_max {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : f x ≤ max (f a) (f b) := by
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  by_cases h : x = a ∨ x = b
  · rcases h with rfl | rfl <;> simp
  · -- x is strictly between a and b
    have hne : x ≠ a := by tauto
    have hne' : x ≠ b := by tauto
    have hxltb : x < b := lt_of_le_of_ne hx.2 hne'
    have haxb : a < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
    -- Write x = s*a + t*b where s = (b-x)/(b-a) and t = (x-a)/(b-a)
    have hba : b - a > 0 := by linarith
    have hbx : b - x > 0 := by linarith
    have hxa : x - a > 0 := by linarith
    set s := (b - x) / (b - a) with hs_def
    set t := (x - a) / (b - a) with ht_def
    have hs_pos : 0 < s := div_pos hbx hba
    have ht_pos : 0 < t := div_pos hxa hba
    have hs_le_one : s ≤ 1 := by rw [div_le_one hba]; linarith [hx.1]
    have ht_le_one : t ≤ 1 := by rw [div_le_one hba]; linarith [hx.2]
    have hst : s + t = 1 := by rw [hs_def, ht_def]; field_simp; ring
    have hx_eq : x = s * a + t * b := by rw [hs_def, ht_def]; field_simp; ring
    have hx_eq' : s • a + t • b = x := by simp [hx_eq, smul_eq_mul]
    have hconv := hf.2 ha_mem hb_mem (le_of_lt hs_pos) (le_of_lt ht_pos) hst
    rw [hx_eq'] at hconv
    -- Now hconv : f(s*a + t*b) ≤ s*f(a) + t*f(b)
    have hle_max : s • f a + t • f b ≤ max (f a) (f b) := by
      have h1 : s • f a + t • f b ≤ s • max (f a) (f b) + t • max (f a) (f b) := by
        apply add_le_add
        · exact smul_le_smul_of_nonneg_left (le_max_left _ _) (le_of_lt hs_pos)
        · exact smul_le_smul_of_nonneg_left (le_max_right _ _) (le_of_lt ht_pos)
      calc s • f a + t • f b ≤ s • max (f a) (f b) + t • max (f a) (f b) := h1
        _ = (s + t) • max (f a) (f b) := by rw [add_smul]
        _ = max (f a) (f b) := by rw [hst]; simp
    linarith

/-- Midpoint convexity: reflecting `x` about the midpoint of `[a,b]`. -/
