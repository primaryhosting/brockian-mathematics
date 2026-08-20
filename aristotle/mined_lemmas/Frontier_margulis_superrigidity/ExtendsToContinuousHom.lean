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

theorem ExtendsToContinuousHom.virtually {Γ : Subgroup G} {rho : Γ →* H}
    (h : ExtendsToContinuousHom Γ rho) : VirtuallyExtendsToContinuousHom Γ rho := by
  obtain ⟨F, hFc, hF⟩ := h
  exact ⟨⊤, inferInstance, F, hFc, fun γ _ => hF γ⟩

/-- Uniqueness of the extension: a continuous homomorphism on `G` is determined by its
restriction to a dense subgroup, provided the target is Hausdorff.  (For a lattice `Γ` in a
connected group `G` the relevant density statement is the density of `Γ` in `G/`(compact), the
point being that the extension in Margulis' theorem is unique whenever it exists on a dense set.) -/
