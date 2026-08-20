/-
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- written as a plain block comment.)

import Mathlib

open scoped Function

namespace Math

/-- The **Chinese Remainder Theorem**: for a finite family of pairwise coprime moduli `n i`,
the ring `ZMod (∏ i, n i)` is isomorphic to the product ring `Π i, ZMod (n i)`. -/

theorem chinese_remainder_crtHom_bijective {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hn : Pairwise (Nat.Coprime on n)) : Function.Bijective (crtHom n) := by
  have h : crtHom n = (ZMod.prodEquivPi n hn : ZMod (∏ i, n i) →+* Π i, ZMod (n i)) :=
    RingHom.ext_zmod _ _
  rw [h]
  exact (ZMod.prodEquivPi n hn).bijective

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

