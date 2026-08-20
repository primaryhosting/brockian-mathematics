/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free: Lean 4 does not allow a module docstring
(`/-! ... -/`) to precede the `import` commands, so the required header comment
forces the development to be self-contained in core Lean.  The primality
predicate is therefore spelled out explicitly (`2 ≤ p ∧ every divisor of p is 1
or p`).  The companion file `RequestProject.GoldbachWheelK2_1327Mathlib`
imports Mathlib and restates the result with `Nat.Prime`.
-/

namespace Brockian

/-- `noFacB n k = true` certifies that no `m` with `2 ≤ m ≤ k` and `m * m ≤ n` divides `n`.
Trial divisions are skipped as soon as `m * m > n`, which keeps kernel evaluation cheap. -/

theorem GoldbachWheelK2_1327_natPrime (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1327) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    GoldbachWheelK2_1327 n h4 hn (Nat.even_iff.mp he)
  exact ⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩

end Brockian

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

