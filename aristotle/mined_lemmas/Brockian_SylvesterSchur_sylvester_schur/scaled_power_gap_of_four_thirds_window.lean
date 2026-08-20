import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma scaled_power_gap_of_four_thirds_window {n i : ℕ} (hi_large : 4840 ≤ i)
    (hi_half : i ≤ n / 2) (hn_lower : 5 * i ≤ 2 * n) (hn_upper : n ^ 3 ≤ i ^ 4) :
    i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i := by
  exact scaled_power_gap_of_deriv_bound (n := n) (i := i) (by omega) hi_half hn_lower (by
    intro z hz
    have hz_pos : 0 < z := by
      have hi_pos : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
      nlinarith [hz.1, hi_pos]
    have hz_nonneg : 0 ≤ z := le_of_lt hz_pos
    have hz_cube_le_n : z ^ (3 : ℕ) ≤ (n : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hz_nonneg hz.2 3
    have hn_cube : (n : ℝ) ^ (3 : ℕ) ≤ (i : ℝ) ^ (4 : ℕ) := by
      exact_mod_cast hn_upper
    exact real_deriv_bound_four_thirds (x := (i : ℝ)) (y := z)
      (by exact_mod_cast hi_large) hz_pos (hz_cube_le_n.trans hn_cube))

