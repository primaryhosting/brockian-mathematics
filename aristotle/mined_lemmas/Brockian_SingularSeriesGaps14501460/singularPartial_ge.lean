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

lemma singularPartial_ge (N : ℕ) : (1 : ℝ) / 2100 ≤ singularPartial gapTuple N := by
  by_cases hN : N + 1 ≤ 11
  · have hsub : (Finset.range (N + 1)).filter Nat.Prime ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      exact primes_lt_eleven hp.2 (by omega)
    have hbound := small_prod_ge _ hsub
    simp only [singularPartial]
    linarith
  · push_neg at hN
    have hsplit : singularPartial gapTuple N
        = (∏ p ∈ (Finset.range 11).filter Nat.Prime, localFactor gapTuple p)
          * ∏ p ∈ (Finset.Ico 11 (N + 1)).filter Nat.Prime, localFactor gapTuple p := by
      simp only [singularPartial, Finset.prod_filter, Finset.range_eq_Ico]
      rw [Finset.prod_Ico_consecutive _ (by omega : 0 ≤ 11) (by omega : 11 ≤ N + 1)]
    have hsub : (Finset.range 11).filter Nat.Prime ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      exact primes_lt_eleven hp.2 hp.1
    have hA := small_prod_ge _ hsub
    have hB := tail_prod_ge N
    rw [hsplit]
    nlinarith [hA, hB]

