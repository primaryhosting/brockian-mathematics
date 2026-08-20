/-
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module docstrings, so the
-- header above is written as an ordinary comment and repeated as a module docstring below.)

import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
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

namespace Frontier

/-! ## The shape of the superrigidity conclusion -/

section Defs

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The conclusion of a superrigidity theorem: the *abstract* group homomorphism
`rho : Γ →* H`, defined on a subgroup `Γ` of a topological group `G`, is the restriction of a
*continuous* homomorphism defined on all of `G`. -/

theorem margulis_superrigidity {G H : Type*} [Group G] [TopologicalSpace G]
    [CommGroup H] [TopologicalSpace H]
    (hH : ∀ (h : H) (n : ℕ), 0 < n → h ^ n = 1 → h = 1)
    (Γ : Subgroup G) [Finite (Abelianization Γ)] (Admissible : (Γ →* H) → Prop) :
    MargulisSuperrigid Γ Admissible := by
  intro rho _
  refine ⟨⊤, inferInstance, 1, continuous_const, fun γ _ => ?_⟩
  simp [hom_trivial_of_abelianization_finite hH Γ rho γ]

/-! ## Non-vacuity of the base case -/

section Sanity

/-- The additive group of the reals, written multiplicatively, is torsion free. -/
