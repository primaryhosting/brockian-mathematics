import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_of_ge_start {m₀ m k : ℕ} (hk : 0 < k) (hm₀ : k < m₀)
    (hle : m₀ ≤ m)
    (hbase : (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  exact Nat.le_induction (m := m₀)
    (P := fun n _ =>
      (n + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (n + k - 1) k)
    hbase
    (fun n hn ih => choose_inequality_succ_start hk (by omega) ih)
    m hle

