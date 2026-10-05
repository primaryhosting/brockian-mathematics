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

theorem exists_fixed_point_ge_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) (a : Ordinal.{u}) : ∃ b : Ordinal.{u}, a ≤ b ∧ f b = b :=
  ⟨nfp f a, le_nfp f a, nfp_fp hf a⟩

end Ordinal

namespace Cardinal

/-- The map `o ↦ (ℵ_ o).ord`, sending an ordinal to the initial ordinal of the
corresponding aleph, is a normal function on the ordinals. -/
