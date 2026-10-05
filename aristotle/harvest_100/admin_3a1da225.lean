/-
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

universe u

namespace Ordinal

/-- Every normal function on the ordinals has a fixed point: the next fixed point
`nfp f a` above any ordinal `a` is one. -/
theorem exists_fixed_point_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) : ∃ a : Ordinal.{u}, f a = a :=
  ⟨nfp f 0, nfp_fp hf 0⟩

/-- Fixed points of a normal function are unbounded: above any ordinal `a`
there is a fixed point of `f`. -/
theorem exists_fixed_point_ge_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) (a : Ordinal.{u}) : ∃ b : Ordinal.{u}, a ≤ b ∧ f b = b :=
  ⟨nfp f a, le_nfp f a, nfp_fp hf a⟩

end Ordinal

namespace Cardinal

/-- The map `o ↦ (ℵ_ o).ord`, sending an ordinal to the initial ordinal of the
corresponding aleph, is a normal function on the ordinals. -/
theorem isNormal_ord_aleph :
    Order.IsNormal (fun o : Ordinal.{u} => (Cardinal.aleph o).ord) :=
  Cardinal.isNormal_ord.comp Cardinal.isNormal_aleph

/-- **Aleph fixed point.** The aleph function, viewed as a normal function on the
ordinals via `o ↦ (ℵ_ o).ord`, has a fixed point: there is an ordinal `o` with
`(ℵ_ o).ord = o`, i.e. `ω_o = o`. -/
theorem aleph_fixed_point_statement :
    ∃ o : Ordinal.{u}, (Cardinal.aleph o).ord = o :=
  Ordinal.exists_fixed_point_of_isNormal isNormal_ord_aleph

/-- The aleph fixed points are unbounded: above every ordinal `a` there is an
ordinal `o` with `(ℵ_ o).ord = o`. -/
theorem exists_aleph_fixed_point_ge (a : Ordinal.{u}) :
    ∃ o : Ordinal.{u}, a ≤ o ∧ (Cardinal.aleph o).ord = o :=
  Ordinal.exists_fixed_point_ge_of_isNormal isNormal_ord_aleph a

end Cardinal

#print axioms Cardinal.aleph_fixed_point_statement

