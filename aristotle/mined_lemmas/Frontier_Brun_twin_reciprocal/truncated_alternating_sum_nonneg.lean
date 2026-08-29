import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

lemma truncated_alternating_sum_nonneg {D : Finset ℕ} {t : ℕ} (ht : Even t) :
    (if D = ∅ then (1 : ℝ) else 0) ≤
      ∑ S ∈ D.powerset with S.card ≤ t, (-1 : ℝ) ^ S.card := by
  have hsplit : ∑ S ∈ D.powerset with S.card ≤ t, (-1 : ℝ) ^ S.card
      = ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * (Nat.choose D.card j) := by
    have : (D.powerset.filter (fun S => S.card ≤ t))
        = (range (t + 1)).biUnion (fun j => D.powersetCard j) := by
      ext S
      simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
      constructor
      · rintro ⟨hS, hc⟩
        exact ⟨S.card, by lia, hS, rfl⟩
      · rintro ⟨j, hj, hS, rfl⟩
        exact ⟨hS, by lia⟩
    rw [this, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_congr rfl (fun S hS => by rw [(mem_powersetCard.1 hS).2]),
        Finset.sum_const, nsmul_eq_mul, card_powersetCard]
      ring
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, mem_powersetCard]
      rintro S ⟨-, rfl⟩ ⟨-, h⟩
      exact hij h
  rw [hsplit]
  rcases Finset.eq_empty_or_nonempty D with rfl | hD
  · have : ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * (Nat.choose (∅ : Finset ℕ).card j) = 1 := by
      refine (Finset.sum_eq_single 0 ?_ ?_).trans (by simp)
      · intro b _ hb
        simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
      · simp
    rw [this]
    simp
  · have hc : D.card ≠ 0 := by simpa using hD.card_pos.ne'
    obtain ⟨s, hs⟩ : ∃ s, D.card = s + 1 := ⟨D.card - 1, by lia⟩
    rw [if_neg hD.ne_empty, hs, alternating_choose_partial]
    have : (0 : ℝ) ≤ (-1 : ℝ) ^ t := by
      rcases ht with ⟨u, hu⟩
      rw [hu, show u + u = 2 * u by ring, pow_mul]
      positivity
    positivity

/-- The main Bonferroni bound: the sifted count is at most the truncated inclusion–exclusion
sum. -/
