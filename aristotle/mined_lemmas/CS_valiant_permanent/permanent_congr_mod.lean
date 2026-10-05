import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/

theorem permanent_congr_mod {m : ℕ} (A B : Matrix ι ι ℤ)
    (h : ∀ i j, ((A i j : ZMod m)) = ((B i j : ZMod m))) :
    ((A.permanent : ZMod m)) = ((B.permanent : ZMod m)) := by
  have hA := permanent_map (Int.castRingHom (ZMod m)) A
  have hB := permanent_map (Int.castRingHom (ZMod m)) B
  have hAB : A.map (Int.castRingHom (ZMod m)) = B.map (Int.castRingHom (ZMod m)) := by
    ext i j
    exact h i j
  have : ((A.permanent : ℤ) : ZMod m) = (Int.castRingHom (ZMod m)) A.permanent := rfl
  rw [this, ← hA, hAB, hB]
  rfl

end CS

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

