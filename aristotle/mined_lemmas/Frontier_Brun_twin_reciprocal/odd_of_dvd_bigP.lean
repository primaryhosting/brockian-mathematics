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

lemma odd_of_dvd_bigP {z d : ℕ} (hd : d ∣ bigP z) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    have h2 : (2:ℕ) ∣ bigP z := he.two_dvd.trans hd
    have h2mem : (2:ℕ) ∈ (bigP z).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, (squarefree_bigP z).ne_zero⟩
    rw [primeFactors_bigP] at h2mem
    exact (mem_oddPrimesBelow.mp h2mem).1 rfl
  · exact ho

/-- The multiplicative function `d ↦ c^ω(d) / d`. -/
