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

/-!
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- The Chinese remainder ring isomorphism `ZMod (m * n) ≃+* ZMod m × ZMod n`
for coprime naturals `m` and `n`. -/
def chineseRemainderEquiv {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- **Chinese remainder theorem**: for coprime naturals `m` and `n`, the ring `ZMod (m * n)`
is ring-isomorphic to the product ring `ZMod m × ZMod n`. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨chineseRemainderEquiv h⟩

/-- The Chinese remainder isomorphism is given by the pair of reduction maps. -/
theorem chineseRemainderEquiv_apply {m n : ℕ} (h : Nat.Coprime m n) (a : ℤ) :
    chineseRemainderEquiv h (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) := by
  simp [chineseRemainderEquiv, ZMod.chineseRemainder, Prod.ext_iff]

end NumberTheory

