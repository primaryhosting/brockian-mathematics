import Mathlib
/-!
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace NumberTheory

/-- **Chinese remainder theorem**: for coprime naturals `m` and `n`, the ring `ZMod (m * n)`
is isomorphic (as a ring) to the product ring `ZMod m × ZMod n`. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

/-- The isomorphism of `NumberTheory.chinese_remainder` can be taken to be the natural one,
given by the pair of reduction maps `ZMod (m * n) → ZMod m` and `ZMod (m * n) → ZMod n`. -/
theorem chinese_remainder_apply {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod (m * n)) :
    (ZMod.chineseRemainder h) a =
      (ZMod.castHom (Dvd.intro n rfl) (ZMod m) a, ZMod.castHom (Dvd.intro_left m rfl) (ZMod n) a) := by
  simp [ZMod.chineseRemainder, Prod.ext_iff, ZMod.castHom_apply]

end NumberTheory

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

