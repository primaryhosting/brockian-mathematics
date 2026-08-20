/-
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
/-!
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace Math

/-- **Fermat's little theorem.** If `p` is prime and `p` does not divide the integer `a`,
then `a ^ (p - 1) ≡ 1 (mod p)`.

This follows from `Int.ModEq.pow_card_sub_one_eq_one` in Mathlib, after converting
non-divisibility by a prime into coprimality. -/

theorem fermat_little_zmod {p : ℕ} (hp : Nat.Prime p) {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 :=
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  ZMod.pow_card_sub_one_eq_one ha

/-- Fermat's little theorem for natural numbers: if `p` is prime and `p ∤ a`, then
`a ^ (p - 1) ≡ 1 (mod p)`. -/
