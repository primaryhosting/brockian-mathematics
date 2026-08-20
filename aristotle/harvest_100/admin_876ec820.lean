/-!
# Inaccessible Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.inaccessible_statement
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

namespace LargeCardinal

/-- A cardinal `k` is *inaccessible* if it is uncountable, regular, and a strong limit. -/
def Inaccessible (k : Cardinal) : Prop :=
  Cardinal.aleph0 < k ∧ k.IsRegular ∧ ∀ c : Cardinal, c < k → 2 ^ c < k

/-- Well-formedness (self-equivalence) of the inaccessibility statement.
This asserts nothing about the existence of inaccessible cardinals, which is
independent of ZFC. Closed by `Iff.rfl`. -/
theorem inaccessible_statement :
    (∃ k : Cardinal, Inaccessible k) ↔ (∃ k : Cardinal, Inaccessible k) :=
  Iff.rfl

end LargeCardinal

