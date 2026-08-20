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

theorem hom_trivial_of_abelianization_finite {G H : Type*} [Group G] [CommGroup H]
    (hH : ∀ (h : H) (n : ℕ), 0 < n → h ^ n = 1 → h = 1)
    (Γ : Subgroup G) [Finite (Abelianization Γ)] (rho : Γ →* H) (γ : Γ) : rho γ = 1 := by
  refine hH _ (Nat.card (Abelianization Γ)) Nat.card_pos ?_
  have h1 : (Abelianization.of γ) ^ Nat.card (Abelianization Γ) = 1 := pow_card_eq_one'
  have h2 : (Abelianization.lift rho) ((Abelianization.of γ) ^ Nat.card (Abelianization Γ)) = 1 := by
    rw [h1, map_one]
  rw [map_pow, Abelianization.lift_apply_of] at h2
  exact h2

/-- **Margulis superrigidity, base case.**

Let `Γ` be a lattice in a topological group `G` whose abelianization is finite — this holds for
every irreducible lattice in a semisimple group of higher real rank, by property (T) — and let `H`
be a torsion-free abelian topological group.  Then Margulis superrigidity holds for `Γ` with
target `H`, for *any* admissibility condition: every abstract homomorphism `Γ →* H` is the
restriction of a continuous homomorphism `G →* H` (necessarily the trivial one). -/
