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

lemma two_sigma_lt_three {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (a : ℕ) :
    2 * ∑ d ∈ (p ^ a).divisors, d < 3 * p ^ a := by
  have hS : ∑ d ∈ (p ^ a : ℕ).divisors, d = ∑ i ∈ Finset.range (a + 1), p ^ i :=
    Nat.sum_divisors_prime_pow hp
  rw [hS]
  set S := ∑ i ∈ Finset.range (a + 1), p ^ i with hSdef
  have hid := pow_mul_geom p a
  have hpos : 0 < p ^ a := pow_pos (by omega) a
  have hSpos : 0 < S := by
    rw [hSdef]
    exact Finset.sum_pos (fun i _ => pow_pos (by omega) i) ⟨0, by simp⟩
  have hpow : p ^ (a + 1) = p * p ^ a := by ring
  nlinarith [hid, hpow]

/-- For a prime `q ≥ 5`, `σ(q ^ b) < (5 / 4) * q ^ b`. -/
