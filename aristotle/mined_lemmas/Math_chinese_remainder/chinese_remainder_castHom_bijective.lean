/-
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Function

namespace Math

/-- **Chinese Remainder Theorem.** For a finite family of pairwise-coprime moduli `a : ι → ℕ`,
the ring `ZMod (∏ i, a i)` is isomorphic to the product ring `Π i, ZMod (a i)`.

The isomorphism is provided by Mathlib's `ZMod.prodEquivPi`. -/

theorem chinese_remainder_castHom_bijective {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Function.Bijective
      (Pi.ringHom fun i : ι =>
        ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))) := by
  have key : ⇑(Pi.ringHom fun i : ι =>
      ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)))
      = ⇑(ZMod.prodEquivPi a coprime) := by
    funext x
    funext i
    have h := RingHom.ext_zmod
      ((Pi.evalRingHom (fun i : ι => ZMod (a i)) i).comp
        (Pi.ringHom fun i : ι =>
          ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))))
      ((Pi.evalRingHom (fun i : ι => ZMod (a i)) i).comp
        (ZMod.prodEquivPi a coprime : ZMod (∏ i, a i) →+* Π i, ZMod (a i)))
    exact congrArg (fun g : ZMod (∏ i, a i) →+* ZMod (a i) => g x) h
  rw [key]
  exact (ZMod.prodEquivPi a coprime).bijective

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

