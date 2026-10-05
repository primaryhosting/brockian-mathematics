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

/-- **Chinese remainder theorem**: if `m` and `n` are coprime natural numbers, then the ring
`ZMod (m * n)` is isomorphic to the product ring `ZMod m × ZMod n`. -/

theorem chinese_remainder_existsUnique {m n : ℕ} (h : Nat.Coprime m n)
    (a : ZMod m) (b : ZMod n) :
    ∃! c : ZMod (m * n), ZMod.castHom (dvd_mul_right m n) (ZMod m) c = a ∧
      ZMod.castHom (dvd_mul_left n m) (ZMod n) c = b := by
  have hcast : ∀ c : ZMod (m * n),
      ZMod.chineseRemainder h c = (ZMod.castHom (dvd_mul_right m n) (ZMod m) c,
        ZMod.castHom (dvd_mul_left n m) (ZMod n) c) := by
    intro c
    simp [ZMod.chineseRemainder, Prod.ext_iff, ZMod.castHom_apply, Prod.fst_zmod_cast,
      Prod.snd_zmod_cast]
  refine ⟨(ZMod.chineseRemainder h).symm (a, b), ?_, ?_⟩
  · have := hcast ((ZMod.chineseRemainder h).symm (a, b))
    rw [RingEquiv.apply_symm_apply] at this
    constructor
    · exact congrArg Prod.fst this.symm
    · exact congrArg Prod.snd this.symm
  · rintro c ⟨hc1, hc2⟩
    have hc : ZMod.chineseRemainder h c = (a, b) := by
      rw [hcast c]
      simp only [ZMod.castHom_apply]
      exact Prod.ext hc1 hc2
    rw [← hc, RingEquiv.symm_apply_apply]

end NumberTheory

