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

/-- The Chinese remainder theorem: for coprime `m n : ℕ`, the ring `ZMod (m * n)` is
ring-isomorphic to `ZMod m × ZMod n`.  This is `ZMod.chineseRemainder` from Mathlib. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

/-- The explicit ring isomorphism `ZMod (m * n) ≃+* ZMod m × ZMod n` for coprime `m`, `n`. -/
def chineseRemainderEquiv {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- The isomorphism is given by reduction modulo `m` and modulo `n`. -/
theorem chineseRemainderEquiv_apply {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    chineseRemainderEquiv h x = (ZMod.castHom (Dvd.intro n rfl) (ZMod m) x,
      ZMod.castHom (Dvd.intro_left m rfl) (ZMod n) x) := by
  simp [chineseRemainderEquiv, ZMod.chineseRemainder, ZMod.castHom_apply, Prod.ext_iff,
    Prod.fst_zmod_cast, Prod.snd_zmod_cast]

end NumberTheory

