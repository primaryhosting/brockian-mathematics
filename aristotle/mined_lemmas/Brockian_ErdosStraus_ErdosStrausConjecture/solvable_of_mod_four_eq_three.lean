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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
`ErdosStrausConjecture` is a well-known open problem, so this file does not prove it
outright.  What is proved here, unconditionally and axiom-cleanly, is:

* `solvable_of_dvd`: solvability passes from a divisor to any positive multiple;
* explicit parametric solutions for `n` even, `3 ∣ n`, `n ≡ 3 (mod 4)`, `n ≡ 2 (mod 3)`
  and `n ≡ 5 (mod 8)`;
* `solvable_of_mod_24_ne_one`: the conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`;
* `erdosStrausConjecture_iff_primes`: the conjecture is *equivalent* to its special case
  for primes `p ≡ 1 (mod 24)`.
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` says that `4 / n` can be written as a sum of three (not necessarily
distinct) positive unit fractions. -/

theorem solvable_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1), 2 * (4 * k + 3) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- If `n = 3k + 2` then `4/n = 1/n + 1/(k+1) + 1/(n(k+1))`. -/
