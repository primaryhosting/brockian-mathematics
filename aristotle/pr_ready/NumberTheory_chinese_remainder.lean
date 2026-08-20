/-!
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Statement: The Chinese remainder theorem: for coprime m n, ZMod (m*n) is ring-isomorphic to (ZMod m) × (ZMod n). State: for m n : Nat with Nat.Coprime m n, there is a ring equivalence ZMod (m*n) ≃+* (ZMod m × ZMod n). (Use Mathlib's ZMod.chineseRemainder.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace NumberTheory

/-- **Chinese remainder theorem**: for coprime naturals `m` and `n`, the ring `ZMod (m * n)`
is ring-isomorphic to the product ring `ZMod m × ZMod n`. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

end NumberTheory

#print axioms NumberTheory.chinese_remainder

