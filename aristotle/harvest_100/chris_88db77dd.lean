/-
# Wilson Theorem
Category: Pure Mathematics
Target: Math.wilson_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Math

/-- **Wilson's Theorem**: for `n > 1`, `n` is prime if and only if
`(n - 1)! ≡ -1 (mod n)`.

The main content is Mathlib's `Nat.prime_iff_fac_equiv_neg_one`
(from `Mathlib/NumberTheory/Wilson.lean`), which states the same equivalence via
`ZMod n`; here it is transferred to the integer congruence `Int.ModEq`. -/
theorem wilson_theorem {n : ℕ} (hn : 1 < n) :
    Nat.Prime n ↔ ((n - 1)! : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
  have h1 : n ≠ 1 := hn.ne'
  rw [Nat.prime_iff_fac_equiv_neg_one h1, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rfl

end Math

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

