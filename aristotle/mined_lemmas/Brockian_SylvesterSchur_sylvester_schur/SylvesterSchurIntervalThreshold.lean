import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

def SylvesterSchurIntervalThreshold : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

/--
The remaining bounded part after the explicit large-start criterion below:
for `k > 1`, it is enough to handle starts up to `k! * 2^(k-1)`.
-/
