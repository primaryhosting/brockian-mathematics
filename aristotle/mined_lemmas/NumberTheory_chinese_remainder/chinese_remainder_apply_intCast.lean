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

theorem chinese_remainder_apply_intCast {m n : ℕ} (h : Nat.Coprime m n) (a : ℤ) :
    ZMod.chineseRemainder h (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) := by
  have h1 : (ZMod.chineseRemainder h) (a : ZMod (m * n))
      = ((ZMod.chineseRemainder h : ZMod (m * n) →+* ZMod m × ZMod n).comp
          (Int.castRingHom (ZMod (m * n)))) a := rfl
  rw [h1, RingHom.eq_intCast'
    ((ZMod.chineseRemainder h : ZMod (m * n) →+* ZMod m × ZMod n).comp
      (Int.castRingHom (ZMod (m * n))))]
  simp [Prod.ext_iff]

/-- Concrete consequence: for coprime `m n`, any pair of residues `(a, b)` is realised by
a single residue modulo `m * n`, and that residue is unique. -/
