import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma primesBelow_succ_card_le (k : ℕ) : (k + 1).primesBelow.card ≤ k := by
  have hsubset : (k + 1).primesBelow ⊆ Finset.Icc 1 k := by
    intro p hp
    rw [Finset.mem_Icc]
    have hlt : p < k + 1 := Nat.lt_of_mem_primesBelow hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    exact ⟨hprime.one_lt.le, Nat.lt_succ_iff.mp hlt⟩
  have hcard := Finset.card_le_card hsubset
  simpa using hcard

