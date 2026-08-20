import Mathlib
open Finset
namespace MS.Inequalities

theorem am_gm_n {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hn : 0 < n) :
    (∏ i, a i) ^ ((1 : ℝ) / n) ≤ (∑ i, a i) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / n) a
    (fun i _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => ha i)
  rw [Real.finset_prod_rpow _ _ (fun i _ => ha i)] at key
  refine key.trans_eq ?_
  simp only
  rw [← Finset.mul_sum]
  ring

