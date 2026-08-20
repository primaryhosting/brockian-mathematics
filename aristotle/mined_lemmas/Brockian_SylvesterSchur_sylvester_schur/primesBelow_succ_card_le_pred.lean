import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma primesBelow_succ_card_le_pred (k : ℕ) : (k + 1).primesBelow.card ≤ k - 1 := by
  by_cases hk : 2 ≤ k
  · have hsubset : (k + 1).primesBelow ⊆ Finset.Icc 2 k := by
      intro p hp
      rw [Finset.mem_Icc]
      have hlt : p < k + 1 := Nat.lt_of_mem_primesBelow hp
      have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
      exact ⟨hprime.two_le, Nat.lt_succ_iff.mp hlt⟩
    have hcard := Finset.card_le_card hsubset
    have hIcc : (Finset.Icc 2 k).card = k - 1 := by
      rw [Nat.card_Icc]
      omega
    simpa [hIcc] using hcard
  · have hk' : k ≤ 1 := by omega
    interval_cases k <;> decide

