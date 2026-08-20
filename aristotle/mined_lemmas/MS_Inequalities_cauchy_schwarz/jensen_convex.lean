import Mathlib
open Finset
namespace MS.Inequalities

theorem jensen_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : f ((∑ i, x i) / n) ≤ (∑ i, f (x i)) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key := hf.map_sum_le (t := Finset.univ) (w := fun _ : Fin n => 1 / (n : ℝ)) (p := x)
    (fun i _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at key
  rw [show (1 / (n : ℝ)) * ∑ i, x i = (∑ i, x i) / n by ring] at key
  exact key.trans_eq (by ring)

