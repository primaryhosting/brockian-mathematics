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

lemma abs_count_range_sub_le (y : ℕ) {d : ℕ} (hd : 0 < d) :
    |(((range y).filter (fun n => d ∣ n * (n + 2))).card : ℝ) - y * (sols d).card / d|
      ≤ (sols d).card := by
  rw [count_range_eq y hd]
  have hsum : (∑ c ∈ sols d, (y / d + if c % d < y % d then 1 else 0))
      = (sols d).card * (y / d) + ((sols d).filter (fun c => c % d < y % d)).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole]
    simp
  rw [hsum]
  push_cast
  have hT : (((sols d).filter (fun c => c % d < y % d)).card : ℝ) ≤ (sols d).card := by
    exact_mod_cast Finset.card_filter_le _ _
  have hT0 : (0:ℝ) ≤ (((sols d).filter (fun c => c % d < y % d)).card : ℝ) := by positivity
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hy : (y : ℝ) = d * (y / d : ℕ) + (y % d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod y d).symm
  have hr : ((y % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt _ hd
  have hr0 : (0:ℝ) ≤ ((y % d : ℕ) : ℝ) := by positivity
  have hs0 : (0:ℝ) ≤ ((sols d).card : ℝ) := by positivity
  have h1 : (d : ℝ) * (y / d : ℕ) * (sols d).card / d = (y / d : ℕ) * (sols d).card := by
    field_simp
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [hy, add_mul, add_div, h1]
    have h2 : ((y % d : ℕ) : ℝ) * (sols d).card / d ≤ (sols d).card := by
      rw [div_le_iff₀ hd']
      nlinarith
    nlinarith
  · rw [hy, add_mul, add_div, h1]
    have h3 : (0:ℝ) ≤ ((y % d : ℕ) : ℝ) * (sols d).card / d := by positivity
    nlinarith

