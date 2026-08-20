import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

def SylvesterSchurInterval : Prop :=
  ∀ ⦃m k : ℕ⦄, 0 < k → k < m →
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

/--
A sufficient binomial-coefficient inequality for Sylvester-Schur, in the
notation of the interval `[m, m + k)`.  This is Granville's Proposition 5.10.1
criterion with `N = m + k - 1` and `π(k)` represented as
`(k + 1).primesBelow.card`.
-/
