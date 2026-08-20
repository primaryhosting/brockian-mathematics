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

noncomputable def twinSieve (x z : ℕ) : BoundingSieve where
  support := (Finset.Icc 1 x).image (fun n => n * (n + 2))
  prodPrimes := bigP z
  prodPrimes_squarefree := squarefree_bigP z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := x
  nu := nu
  nu_mult := nu_mult
  nu_pos_of_prime := fun p hp _ => by
    rw [nu_prime hp]
    have : (0:ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp hdvd => by
    rw [nu_prime hp]
    have hmem : p ∈ oddPrimesBelow z := by
      rw [← primeFactors_bigP z, Nat.mem_primeFactors]
      exact ⟨hp, hdvd, (squarefree_bigP z).ne_zero⟩
    have hp2 : p ≠ 2 := (mem_oddPrimesBelow.mp hmem).1
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have h3' : (3:ℝ) ≤ p := by exact_mod_cast h3
    rw [div_lt_one (by linarith)]
    linarith

/-- The sifted sum of `twinSieve` counts the `n ∈ [1, x]` with `n (n+2)` coprime to all
odd primes `≤ z`. -/
