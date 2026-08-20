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

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* when its set of divisors can be split into
two parts with equal sums, i.e. there is `S ⊆ n.divisors` whose sum is half of `σ₁ n`. -/

theorem primeFactors_945 : (945 : ℕ).primeFactors = {3, 5, 7} := by
  have h : (945 : ℕ) = 3 ^ 3 * (5 * 7) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-- **Odd Zumkeller From 3 Structure.**
Every odd Zumkeller number has at least three distinct prime factors, and this is sharp:
`945 = 3³·5·7` is an odd Zumkeller number with exactly three distinct prime factors, and
`945 * m` is an odd Zumkeller number for every odd `m` coprime to `945`. -/
