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

theorem mulWitness_completelyMultiplicative : CompletelyMultiplicative mulWitness := by
  intro a b ha hb
  have hperm := Nat.perm_primeFactorsList_mul (a := a) (b := b) (by omega) (by omega)
  have hlen : (a * b).primeFactorsList.length =
      a.primeFactorsList.length + b.primeFactorsList.length := by
    rw [hperm.length_eq, List.length_append]
  have hcount : (a * b).primeFactorsList.count 7 =
      a.primeFactorsList.count 7 + b.primeFactorsList.count 7 := by
    rw [hperm.count_eq, List.count_append]
  unfold mulWitness
  rw [hlen, hcount, show a.primeFactorsList.length + b.primeFactorsList.length +
      (a.primeFactorsList.count 7 + b.primeFactorsList.count 7) =
      (a.primeFactorsList.length + a.primeFactorsList.count 7) +
      (b.primeFactorsList.length + b.primeFactorsList.count 7) from by ring, pow_add]

