import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

theorem abs_count_sub_le (x : ℕ) {d : ℕ} (hodd : Odd d) (hsq : Squarefree d) :
    |((((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ))
        - x * 2 ^ d.primeFactors.card / d| ≤ 2 * 2 ^ d.primeFactors.card := by
  have hd : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hcs : ((sols d).card : ℝ) = 2 ^ d.primeFactors.card := by
    rw [card_sols d hodd hsq]; push_cast; ring
  have hA := abs_count_range_sub_le (x + 1) hd
  rw [count_Icc_add_one x d] at hA
  rw [abs_le] at hA ⊢
  set C := ((((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)) with hC
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hs1 : (1:ℝ) ≤ ((sols d).card : ℝ) := by exact_mod_cast one_le_card_sols hd
  have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsd : ((sols d).card : ℝ) / d ≤ ((sols d).card : ℝ) := by
    rw [div_le_iff₀ hd']
    nlinarith
  have hsd0 : (0:ℝ) ≤ ((sols d).card : ℝ) / d := by positivity
  have hexp : ((x + 1 : ℕ) : ℝ) * ((sols d).card : ℝ) / d
      = (x : ℝ) * ((sols d).card : ℝ) / d + ((sols d).card : ℝ) / d := by
    push_cast
    ring
  rw [hexp] at hA
  push_cast at hA
  rw [← hcs]
  constructor <;> [linarith [hA.1]; linarith [hA.2]]

end Brun

import RequestProject.Brun.Bonferroni
import RequestProject.Brun.SolutionCount
import RequestProject.Brun.PrimeProducts

/-!
# Brun's pure sieve applied to the twin prime problem

We set up the sieve problem for the sequence `n (n+2)`, `1 ≤ n ≤ x`, sifted by the odd primes
`p ≤ z`, and combine Brun's truncated Möbius weights with the two estimates of
`RequestProject.Brun.PrimeProducts` to obtain an upper bound for the number of twin primes
up to `x`.
-/

open Finset

namespace Brun

/-- The number of primes `p ≤ x` such that `p + 2` is also prime. -/
