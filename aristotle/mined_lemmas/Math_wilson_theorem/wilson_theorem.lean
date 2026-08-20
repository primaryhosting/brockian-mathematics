/-
# Wilson Theorem
Category: Pure Mathematics
Target: Math.wilson_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

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

set_option grind.warning false

namespace Math

/-- **Wilson's Theorem**: for `n > 1`, `n` is prime if and only if
`(n - 1)! ≡ -1 (mod n)` (congruence stated over the integers).

The core content is Mathlib's `Nat.prime_iff_fac_equiv_neg_one`
(itself built on `ZMod.wilsons_lemma`); here we transport it from an
equation in `ZMod n` to an `Int.ModEq` statement. -/

theorem wilson_theorem (n : ℕ) (hn : 1 < n) :
    Nat.Prime n ↔ ((n - 1)! : ℤ) ≡ -1 [ZMOD n] := by
  rw [Nat.prime_iff_fac_equiv_neg_one hn.ne', ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rfl

end Math
#print axioms Math.wilson_theorem

