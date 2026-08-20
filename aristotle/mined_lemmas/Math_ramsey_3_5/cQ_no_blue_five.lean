import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma cQ_no_blue_five :
    ∀ t ∈ (Finset.range 13).powersetCard 5,
      ¬ (∀ x ∈ t, ∀ y ∈ t, x ≠ y → cQ x y = false) := by decide

end Ramsey

namespace Math

/-- **The Ramsey number `R(3,5)` equals `14`**: `14` is the least `N` such that every
graph on `N` vertices contains a triangle or an independent set of size `5`. -/
