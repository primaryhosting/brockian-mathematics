import Mathlib
/-!
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
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

namespace Math

/-- **Lagrange's theorem**: the order of a subgroup `H` of a finite group `G`
divides the order of `G`.

The proof is the standard coset decomposition: `G` is partitioned by the left
cosets of `H`, each of which is in bijection with `H`, so `|G| = [G : H] * |H|`. -/
theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype.card H ∣ Fintype.card G := by
  classical
  refine ⟨Fintype.card (G ⧸ H), ?_⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (s := H)
  simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using h

end Math

