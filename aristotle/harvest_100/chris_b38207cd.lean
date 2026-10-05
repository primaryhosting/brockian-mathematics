/-
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- **Chinese remainder theorem** (ring-theoretic form): for coprime naturals `m` and `n`,
the ring `ZMod (m * n)` is isomorphic to the product ring `ZMod m × ZMod n`. -/
noncomputable def chineseRemainderEquiv {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- **Chinese remainder theorem**: for coprime naturals `m` and `n`, there exists a ring
equivalence `ZMod (m * n) ≃+* ZMod m × ZMod n`. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨chineseRemainderEquiv h⟩

/-- The isomorphism is the natural one: it sends the class of an integer `a` modulo `m * n`
to the pair of its classes modulo `m` and modulo `n`. -/
theorem chineseRemainderEquiv_apply_intCast {m n : ℕ} (h : Nat.Coprime m n) (a : ℤ) :
    chineseRemainderEquiv h (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) := by
  have h1 : (chineseRemainderEquiv h) (a : ZMod (m * n)) = ((a : ZMod m × ZMod n)) :=
    map_intCast (chineseRemainderEquiv h : ZMod (m * n) →+* ZMod m × ZMod n) a
  rw [h1]
  rfl

end NumberTheory

