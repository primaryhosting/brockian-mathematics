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

set_option grind.warning false

namespace Cardinal

/-- Every normal function on the ordinals has a fixed point: the normal-function
fixed point `Ordinal.nfp f a` is one. -/

theorem aleph_fixed_point_statement : ∃ o : Ordinal, (Cardinal.aleph o).ord = o := by
  obtain ⟨o, ho⟩ := exists_fixed_point_of_isNormal Ordinal.isNormal_omega
  exact ⟨o, by rw [Cardinal.ord_aleph]; exact ho⟩

end Cardinal

