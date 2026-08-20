import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/

lemma localFactor_pos_of_small_primes (G : Finset ℕ)
    (h : ∀ q : ℕ, q.Prime → q ≤ G.card → nu G q < q) (p : ℕ) :
    0 < localFactor G p := by
  unfold localFactor
  split_ifs with hp
  · have hp2 : 2 ≤ p := hp.two_le
    have hp0 : (0 : ℝ) < p := by positivity
    have hnu : nu G p < p := by
      by_cases hle : p ≤ G.card
      · exact h p hp hle
      · exact lt_of_le_of_lt (nu_le_card G p) (by omega)
    have hnum : 0 < 1 - (nu G p : ℝ) / p := by
      have : (nu G p : ℝ) / p < 1 := by
        rw [div_lt_one hp0]; exact_mod_cast hnu
      linarith
    have hden : 0 < (1 - 1 / (p : ℝ)) ^ G.card := by
      apply pow_pos
      have : (1 : ℝ) / p ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left <;> [norm_num; norm_num; exact_mod_cast hp2]
      linarith
    exact div_pos hnum hden
  · norm_num

/-- Positivity of every local factor for the admissible 5-tuple `{0,2,6,8,12}`
    (extends the verified twin/triple/quadruple positivity to k = 5). -/
