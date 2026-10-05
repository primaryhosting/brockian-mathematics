/-
# Wilson Theorem
Category: Pure Mathematics
Target: Math.wilson_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wilson Theorem
Category: Pure Mathematics
Target: Math.wilson_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Math

/-- **Wilson's theorem.** For a natural number `n > 1`, `n` is prime if and only if
`(n - 1)! ≡ -1 (mod n)`. -/
theorem wilson_theorem {n : ℕ} (hn : 1 < n) :
    Nat.Prime n ↔ ((n - 1)! : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
  have hcast : (((n - 1)! : ℤ) ≡ -1 [ZMOD (n : ℤ)]) ↔ (((n - 1)! : ℕ) : ZMod n) = -1 := by
    rw [Int.ModEq]
    constructor
    · intro h
      have : ((((n - 1)! : ℕ) : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).2 h
      simpa using this
    · intro h
      have : ((((n - 1)! : ℕ) : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) := by
        push_cast
        simpa using h
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1 this
  rw [hcast, ← Nat.prime_iff_fac_equiv_neg_one (Nat.ne_of_gt hn), Nat.prime_iff]

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

