/-
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- **Lagrange's theorem.** The order of a subgroup `H` of a finite group `G`
divides the order of `G`.

The proof is the classical one: `G` decomposes into left cosets of `H`, each in
bijection with `H`, so `|G| = [G : H] * |H|`. -/
theorem lagrange_subgroup {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G := by
  have hbij : Nat.card (G ⧸ H) * Nat.card H = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup H).symm
  exact Dvd.intro_left _ hbij

end Math

