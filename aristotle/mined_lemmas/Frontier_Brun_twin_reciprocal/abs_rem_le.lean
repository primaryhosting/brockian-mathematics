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

lemma abs_rem_le (x z : ℕ) {d : ℕ} (hd : d ∣ bigP z) :
    |BoundingSieve.rem (s := twinSieve x z) d| ≤ 2 * 2 ^ d.primeFactors.card := by
  have hdne : d ≠ 0 := by
    rintro rfl
    exact (squarefree_bigP z).ne_zero (zero_dvd_iff.mp hd)
  have hsq : Squarefree d := (squarefree_bigP z).squarefree_of_dvd hd
  have hodd : Odd d := odd_of_dvd_bigP hd
  have := abs_count_sub_le x hodd hsq
  rw [BoundingSieve.rem, multSum_twinSieve]
  have hnu : (twinSieve x z).nu d = 2 ^ d.primeFactors.card / d := nu_apply hdne
  have hmass : (twinSieve x z).totalMass = (x : ℝ) := rfl
  rw [hnu, hmass]
  calc |(((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)
        - 2 ^ d.primeFactors.card / d * x|
      = |(((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2))).card : ℝ)
        - x * 2 ^ d.primeFactors.card / d| := by ring_nf
    _ ≤ 2 * 2 ^ d.primeFactors.card := this

