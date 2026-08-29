import Mathlib

/-!
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
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

namespace NumberTheory

/-- **Chinese remainder theorem**: if `m` and `n` are coprime natural numbers, then
`ZMod (m * n)` is isomorphic, as a ring, to `ZMod m × ZMod n`.

This is Mathlib's `ZMod.chineseRemainder`. -/

theorem chineseRemainderEquiv_apply {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    chineseRemainderEquiv h x = (ZMod.castHom (Dvd.intro n rfl) (ZMod m) x,
      ZMod.castHom (Dvd.intro_left m rfl) (ZMod n) x) := by
  ext <;> simp [chineseRemainderEquiv, ZMod.chineseRemainder]

end NumberTheory

#print axioms NumberTheory.chinese_remainder
#print axioms NumberTheory.chineseRemainderEquiv_apply

