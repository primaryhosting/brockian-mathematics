import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma small_prod_ge (s : Finset ℕ) (hs : s ⊆ ({2, 3, 5, 7} : Finset ℕ)) :
    (1 : ℝ) / 210 ≤ ∏ p ∈ s, localFactor gapTuple p := by
  have hprime : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    have := hs hp
    fin_cases this <;> norm_num
  have h1 : ∏ p ∈ s, (1 : ℝ) / (p : ℝ) ≤ ∏ p ∈ s, localFactor gapTuple p := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have := (hprime p hp).two_le
      have : (0:ℝ) < (p:ℝ) := by
        have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hprime p hp).two_le
        linarith
      positivity
    · intro p hp
      exact inv_le_localFactor (hprime p hp)
  have hdvd : (∏ p ∈ s, p) ∣ (∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hs
  have hval : (∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), p) = 210 := by decide
  rw [hval] at hdvd
  have hple : (∏ p ∈ s, p) ≤ 210 := Nat.le_of_dvd (by norm_num) hdvd
  have hppos : 0 < ∏ p ∈ s, p := by
    refine Finset.prod_pos fun p hp => ?_
    exact (hprime p hp).pos
  have h2 : (1 : ℝ) / 210 ≤ ∏ p ∈ s, (1 : ℝ) / (p : ℝ) := by
    have hcast : ∏ p ∈ s, (1 : ℝ) / (p : ℝ) = 1 / ((∏ p ∈ s, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      rw [Finset.prod_div_distrib]
      simp
    rw [hcast]
    have h1' : (0:ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by exact_mod_cast hppos
    have h2' : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ 210 := by exact_mod_cast hple
    exact one_div_le_one_div_of_le h1' h2'
  linarith

