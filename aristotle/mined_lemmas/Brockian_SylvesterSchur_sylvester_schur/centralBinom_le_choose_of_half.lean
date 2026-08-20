import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma centralBinom_le_choose_of_half {n i : ℕ} (hi_half : i ≤ n / 2) :
    i.centralBinom ≤ Nat.choose n i := by
  have htwice : 2 * i ≤ n := by omega
  simpa [Nat.centralBinom] using Nat.choose_le_choose i htwice

