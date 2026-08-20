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

/-- **Fixed point theorem for normal functions.** Every normal function on the ordinals has a
fixed point; indeed the next fixed point `nfp f 0` above `0` is one.
This is `Ordinal.nfp_fp` from Mathlib, packaged as an existence statement. -/
theorem exists_fixed_point_of_isNormal {f : Ordinal.{u} → Ordinal.{u}} (hf : Order.IsNormal f) :
    ∃ a : Ordinal.{u}, f a = a :=
  ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩

end Ordinal

namespace Cardinal

/-- **The aleph function has a fixed point.**

The map `o ↦ (aleph o).ord`, i.e. Mathlib's `Ordinal.omega` (`ω_`), is a normal function on the
ordinals, hence by the fixed point theorem for normal functions
(`Ordinal.exists_fixed_point_of_isNormal`, based on Mathlib's `Ordinal.nfp_fp`) it has a fixed
point: there is an ordinal `o` with `(aleph o).ord = o`. -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal.{u}, (Cardinal.aleph o).ord = o := by
  obtain ⟨o, ho⟩ :=
    Ordinal.exists_fixed_point_of_isNormal
      (f := fun o : Ordinal.{u} => Ordinal.omega o) Ordinal.isNormal_omega
  exact ⟨o, by rw [Cardinal.ord_aleph]; exact ho⟩

end Cardinal

#print axioms Cardinal.aleph_fixed_point_statement

