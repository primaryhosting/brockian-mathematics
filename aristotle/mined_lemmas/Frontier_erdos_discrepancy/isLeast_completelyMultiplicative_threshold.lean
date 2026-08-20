import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem isLeast_completelyMultiplicative_threshold :
    IsLeast {N : ℕ | ∀ f : ℕ → ℤ, CompletelyMultiplicative f → IsPMOne f →
      2 ≤ discrepancyUpTo f N} 10 := by
  constructor
  · intro f hcm hf
    exact two_le_discrepancyUpTo_ten_of_completelyMultiplicative hcm hf
  · intro N hN
    by_contra hlt
    have h9 : N ≤ 9 := by omega
    have h1 : 2 ≤ discrepancyUpTo mulWitness N :=
      hN mulWitness mulWitness_completelyMultiplicative mulWitness_pm_one
    have h2 : discrepancyUpTo mulWitness N ≤ 1 :=
      le_trans (discrepancyUpTo_mono h9) discrepancyUpTo_mulWitness_nine
    omega

end Frontier

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `homogSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`, the sum of `f` along the
initial segment of length `n` of the homogeneous arithmetic progression with
common difference `d`. -/
