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
noncomputable def chinese_remainder {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) : ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime

/-- Each modulus divides the product of all the moduli. -/
theorem dvd_prod {ι : Type*} [Fintype ι] (a : ι → ℕ) (i : ι) : a i ∣ ∏ j, a j :=
  Finset.dvd_prod_of_mem a (Finset.mem_univ i)

/-- The isomorphism of the Chinese Remainder Theorem is the natural one: its `i`-th component
is reduction modulo `a i`. -/
theorem chinese_remainder_apply {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) (x : ZMod (∏ i, a i)) (i : ι) :
    chinese_remainder a coprime x i = ZMod.castHom (dvd_prod a i) (ZMod (a i)) x := by
  have h : ((Pi.evalRingHom (fun i ↦ ZMod (a i)) i).comp
      (chinese_remainder a coprime : ZMod (∏ i, a i) →+* Π i, ZMod (a i)))
      = ZMod.castHom (dvd_prod a i) (ZMod (a i)) := Subsingleton.elim _ _
  exact congrArg (fun f : ZMod (∏ i, a i) →+* ZMod (a i) => f x) h

/-- Cardinality form: the two rings have the same (finite) size when all moduli are positive. -/
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

