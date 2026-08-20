import Mathlib

/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
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

namespace AdditiveComb

open Classical in
/-- For an integer `d`, a chosen pair `(a, c) ∈ A × C` with `a - c = d`, whenever `d ∈ A - C`
(and a junk value otherwise). -/

noncomputable def subWitness (A C : Finset ℤ) (d : ℤ) : ℤ × ℤ :=
  if h : ∃ p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ C ∧ p.1 - p.2 = d then h.choose else (0, 0)

/-- The defining property of `subWitness`: for `d ∈ A - C` it is a genuine representation of `d`
as a difference of an element of `A` and an element of `C`. -/
