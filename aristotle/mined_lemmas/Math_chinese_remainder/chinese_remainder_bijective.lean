/-
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Function -- for the `on` notation

namespace Math

/-- **Chinese Remainder Theorem.**  For a finite family of pairwise coprime moduli `a i`,
the ring `ZMod (∏ i, a i)` is isomorphic to the product ring `Π i, ZMod (a i)`.

This is `ZMod.prodEquivPi` from Mathlib (`Mathlib/Data/ZMod/QuotientRing.lean`). -/

theorem chinese_remainder_bijective {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Function.Bijective (fun (x : ZMod (∏ i, a i)) (i : ι) =>
      ZMod.castHom (dvd_prod a i) (ZMod (a i)) x) := by
  have : (fun (x : ZMod (∏ i, a i)) (i : ι) =>
      ZMod.castHom (dvd_prod a i) (ZMod (a i)) x) = chinese_remainder a coprime := by
    funext x i
    exact (chinese_remainder_apply a coprime x i).symm
  rw [this]
  exact (chinese_remainder a coprime).bijective

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

