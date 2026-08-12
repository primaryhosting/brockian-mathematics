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


/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Ordinal

/-- Every normal function on the ordinals has a fixed point: its normal fixed point
sequence `nfp f a` started at any `a` is one. -/
theorem exists_fixed_point_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) : ∃ a : Ordinal.{u}, f a = a :=
  ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩

end Ordinal

namespace Cardinal

/-- **Aleph fixed point.** The aleph function, viewed as a normal function on ordinals
(`o ↦ (aleph o).ord = ω_ o`), has a fixed point: there is an ordinal `o` with
`(aleph o).ord = o`. -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal.{u}, (Cardinal.aleph o).ord = o := by
  obtain ⟨o, ho⟩ := Ordinal.exists_fixed_point_of_isNormal Ordinal.isNormal_omega
  exact ⟨o, by rwa [Cardinal.ord_aleph]⟩

end Cardinal

