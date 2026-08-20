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

lemma nuc_mult (c : ℝ) : (nuc c).IsMultiplicative := by
  constructor
  · simp [nuc]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [nuc]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Nat.coprime_zero_right] at hmn
      subst hmn
      simp [nuc]
    have hcard : (m * n).primeFactors.card = m.primeFactors.card + n.primeFactors.card := by
      rw [Nat.primeFactors_mul hm hn,
        Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hmn)]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [nuc, ArithmeticFunction.coe_mk, mul_eq_zero, hm, hn, or_self, if_false]
    rw [hcard]
    push_cast
    rw [pow_add]
    field_simp

/-- The density function of the sieve: `ν d = 2^ω(d) / d`. -/
