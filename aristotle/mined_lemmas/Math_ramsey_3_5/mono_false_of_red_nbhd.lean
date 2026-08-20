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

theorem mono_false_of_red_nbhd (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S) {v : V} {S : Finset V}
    (hvS : v ∉ S) (h : ∀ u ∈ S, c v u = true) : Mono c false S := by
  intro u hu w hw huw
  by_contra hne
  have hcuw : c u w = true := by
    cases hc : c u w with
    | false => exact absurd hc hne
    | true => rfl
  have hvu : v ≠ u := by rintro rfl; exact hvS hu
  have hvw : v ≠ w := by rintro rfl; exact hvS hw
  exact no_red_triple hsymm hno3 hvu hvw huw (h u hu) (h w hw) hcuw

/-- Handshake lemma (parity form): for a symmetric irreflexive relation, the sum over a
finite set `T` of the number of `T`-neighbours is even. -/
