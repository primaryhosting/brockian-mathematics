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

set_option grind.warning false

namespace Cardinal

/-- Every normal function on the ordinals has a fixed point: the normal-function
fixed-point theorem, obtained from the least fixed point `Ordinal.nfp f 0` above `0`. -/
theorem exists_fixedPoint_of_isNormal {f : Ordinal → Ordinal} (hf : Order.IsNormal f) :
    ∃ a : Ordinal, f a = a :=
  ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩

/-- The map `o ↦ (ℵ_ o).ord`, sending an ordinal to the initial ordinal of the corresponding
aleph, is a normal function on the ordinals. -/
theorem isNormal_ord_aleph : Order.IsNormal fun o : Ordinal => (aleph o).ord :=
  isNormal_ord.comp isNormal_aleph

/-- **Aleph fixed point**: the aleph function, viewed as a normal function on the ordinals
via `o ↦ (ℵ_ o).ord`, has a fixed point. That is, there is an ordinal `o` whose associated
cardinal `ℵ_ o` has `o` itself as its initial ordinal. -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal, (aleph o).ord = o :=
  exists_fixedPoint_of_isNormal isNormal_ord_aleph

end Cardinal

#print axioms Cardinal.aleph_fixed_point_statement

