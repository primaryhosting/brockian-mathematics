import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_succ_start {m k : ℕ} (hk : 0 < k) (hm : k < m)
    (h : (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k) :
    (m + 1 + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + 1 + k - 1) k := by
  have hN : k ≤ m + k - 1 := by omega
  have hsucc := choose_inequality_succ (N := m + k - 1) (k := k)
    (r := (k + 1).primesBelow.card) hN (primesBelow_succ_card_le k) h
  have hN' : m + k - 1 + 1 = m + 1 + k - 1 := by omega
  simpa [hN'] using hsucc

