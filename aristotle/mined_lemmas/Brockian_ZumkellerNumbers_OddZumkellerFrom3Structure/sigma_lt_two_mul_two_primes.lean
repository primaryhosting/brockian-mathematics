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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

lemma sigma_lt_two_mul_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h3 : 3 ≤ p) (h5 : 5 ≤ q) (hne : p ≠ q) (e f : ℕ) :
    ∑ d ∈ (p ^ e * q ^ f).divisors, d < 2 * (p ^ e * q ^ f) := by
  have hcop : Nat.Coprime (p ^ e) (q ^ f) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hne)
  rw [Nat.Coprime.sum_divisors_mul hcop]
  have h1 := two_sigma_lt_three hp h3 e
  have h2 := four_sigma_lt_five hq h5 f
  have hep : 0 < p ^ e := pow_pos (by omega) e
  have hfq : 0 < q ^ f := pow_pos (by omega) f
  have hprod : (2 * ∑ d ∈ (p ^ e).divisors, d) * (4 * ∑ d ∈ (q ^ f).divisors, d)
      < (3 * p ^ e) * (5 * q ^ f) := Nat.mul_lt_mul_of_lt_of_lt h1 h2
  by_contra hcon
  push_neg at hcon
  have hPQ : 0 < p ^ e * q ^ f := Nat.mul_pos hep hfq
  nlinarith [hprod, hcon, hPQ]

/-- A prime `≥ 3` which is not `3` is `≥ 5`. -/
