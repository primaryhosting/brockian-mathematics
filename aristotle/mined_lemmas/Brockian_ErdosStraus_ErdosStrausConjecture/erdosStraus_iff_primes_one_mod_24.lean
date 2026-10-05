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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Erdős–Straus conjecture asserts that for every integer `n ≥ 2` the fraction
`4/n` can be written as a sum of three positive unit fractions.  The conjecture
is open, so what is proved here is a *conditional reduction*: the full statement
follows from the special case of primes `p ≡ 1 (mod 24)`.

Unconditionally we prove solvability for every `n ≥ 2` that has a divisor `≥ 2`
which is not congruent to `1` modulo `24`; in particular for every `n ≥ 2` with
`n % 24 ≠ 1`.
-/

namespace Brockian.ErdosStraus

/-- `4/n` is a sum of three positive unit fractions. -/

theorem erdosStraus_iff_primes_one_mod_24 :
    (∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → ErdosStrausSolvable p) := by
  refine ⟨fun h p hp _ => h p hp.two_le, ErdosStrausConjecture⟩

end Brockian.ErdosStraus

