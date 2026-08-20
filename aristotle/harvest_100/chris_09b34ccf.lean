/-
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Verification: pending
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

/-- **Chinese remainder theorem**: if `m` and `n` are coprime natural numbers, then
`ZMod (m * n)` is isomorphic, as a ring, to `ZMod m × ZMod n`. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

/-- The explicit ring equivalence witnessing the Chinese remainder theorem. -/
def chineseRemainderEquiv {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- The equivalence of the Chinese remainder theorem is given by reduction modulo `m`
and modulo `n`. -/
theorem chineseRemainderEquiv_apply {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    chineseRemainderEquiv h x =
      (ZMod.castHom (Dvd.intro n rfl) (ZMod m) x, ZMod.castHom (Dvd.intro_left m rfl) (ZMod n) x) :=
  Prod.ext (Prod.fst_zmod_cast x) (Prod.snd_zmod_cast x)

end NumberTheory

