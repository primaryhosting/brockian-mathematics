/-
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
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

universe u

namespace Ordinal

/-- Key intermediate lemma: every normal function on the ordinals has a fixed point.
The witness is the least fixed point above `0`, given by the normal-function iteration
`Ordinal.nfp`. -/
theorem exists_fixedPoint_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) : ∃ a : Ordinal.{u}, f a = a :=
  ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩

end Ordinal

namespace Cardinal

/-- The map sending an ordinal `o` to the ordinal `(ℵ_ o).ord` is a normal function. -/
theorem isNormal_ord_aleph : Order.IsNormal (fun o : Ordinal.{u} => (Cardinal.aleph o).ord) := by
  simp only [Cardinal.ord_aleph]
  exact Ordinal.isNormal_omega

/-- **Aleph fixed point.** The aleph function, viewed as a normal function on ordinals via
`o ↦ (ℵ_ o).ord`, has a fixed point: there is an ordinal `o` with `(ℵ_ o).ord = o`
(equivalently, `ℵ_ o` is the `o`-th infinite cardinal *and* has cardinality index `o`). -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal.{u}, (Cardinal.aleph o).ord = o :=
  Ordinal.exists_fixedPoint_of_isNormal isNormal_ord_aleph

end Cardinal

