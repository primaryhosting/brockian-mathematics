import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_le_chord {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f x ≤ f a + (x - a) / (b - a) * (f b - f a) := by
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr (le_of_lt hab)
  have hb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr (le_of_lt hab)
  set t : ℝ := (x - a) / (b - a) with ht_def
  have ht_nonneg : 0 ≤ t := div_nonneg (by linarith [hx.1]) (by linarith)
  have ht_le_one : t ≤ 1 := by rw [div_le_one (by linarith : 0 < b - a)]; linarith [hx.2]
  have hba_pos : 0 < b - a := by linarith
  have hx_eq : x = (1 - t) * a + t * b := by
    rw [ht_def]
    field_simp
    ring
  have hconv := hf.2 ha hb (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ t) (by ring)
  calc f x = f ((1 - t) * a + t * b) := by rw [hx_eq]
    _ ≤ (1 - t) * f a + t * f b := hconv
    _ = f a + t * (f b - f a) := by ring
    _ = f a + (x - a) / (b - a) * (f b - f a) := by rw [ht_def]

/-- The right-hand Hermite–Hadamard inequality, in unnormalized form. -/
