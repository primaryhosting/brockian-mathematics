import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

def SylvesterSchurChooseInequality : Prop :=
  ∀ ⦃m k : ℕ⦄, 0 < k → k < m →
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k

/--
For each interval length `k`, a threshold `m₀` where Granville's binomial
inequality holds, together with direct interval checks below that threshold.
The monotonicity lemma below propagates the threshold case to all larger
starts, where the binomial criterion supplies the interval witness.
-/
