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

theorem extension_unique_of_dense [T2Space H] {Γ : Subgroup G} (hΓ : Dense (Γ : Set G))
    {F₁ F₂ : G →* H} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (h : ∀ γ : Γ, F₁ (γ : G) = F₂ (γ : G)) : F₁ = F₂ :=
  DFunLike.coe_injective (Continuous.ext_on hΓ h₁ h₂ fun x hx => h ⟨x, hx⟩)

end Basic

/-! ## A Lean-checked reduction: extension from a dense subgroup -/

section DenseExtension

variable {G H : Type*} [UniformSpace G] [Group G] [IsUniformGroup G]
  [UniformSpace H] [Group H] [IsUniformGroup H] [CompleteSpace H] [T2Space H]

/-- **Reduction of the superrigidity conclusion to a uniform-continuity estimate.**

If `Γ ≤ G` is a *dense* subgroup and the abstract homomorphism `rho : Γ →* H` is uniformly
continuous for the uniformity induced from `G`, then `rho` does extend to a continuous homomorphism
`G →* H` (the target being a complete Hausdorff group).  This is the standard "soft" half of a
superrigidity argument: all the work is in producing the uniform continuity estimate. -/
