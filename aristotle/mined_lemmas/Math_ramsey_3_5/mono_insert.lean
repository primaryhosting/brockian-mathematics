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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/

theorem mono_insert (hsymm : ∀ u v, c u v = c v u) {col : Bool} {v : V} {S : Finset V}
    (hS : Mono c col S) (hv : ∀ u ∈ S, c v u = col) (hvS : v ∉ S) :
    Mono c col (insert v S) := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact absurd rfl hxy
    · exact hv y hy'
  · rcases Finset.mem_insert.mp hy with rfl | hy'
    · rw [hsymm]; exact hv x hx'
    · exact hS x hx' y hy' hxy

/-- In a colouring with no red triangle, the red neighbourhood of a vertex is blue. -/
