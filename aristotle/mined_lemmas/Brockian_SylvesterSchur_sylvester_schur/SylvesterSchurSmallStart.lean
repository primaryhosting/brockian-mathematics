import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

def SylvesterSchurSmallStart : Prop :=
  ∀ ⦃m k : ℕ⦄, 1 < k → k < m → m ≤ k.factorial * 2 ^ (k - 1) →
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

section RealInequalities

open Real

