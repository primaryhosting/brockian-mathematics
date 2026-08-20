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

theorem extendsToContinuousHom_of_dense_of_uniformContinuous {Γ : Subgroup G}
    (hΓ : Dense (Γ : Set G)) (rho : Γ →* H)
    (hrho : UniformContinuous fun x : (Γ : Set G) => rho ⟨(x : G), x.2⟩) :
    ExtendsToContinuousHom Γ rho := by
  set g : ((Γ : Set G)) → H := fun x => rho ⟨(x : G), x.2⟩
  set f : G → H := hΓ.extend g
  have hfc : Continuous f := (hΓ.uniformContinuous_extend hrho).continuous
  have hval : ∀ x : G, ∀ hx : x ∈ Γ, f x = rho ⟨x, hx⟩ := fun x hx =>
    hΓ.extend_of_ind hrho ⟨x, hx⟩
  have hmul : ∀ a b : G, f (a * b) = f a * f b := by
    have hd : Dense ((Γ : Set G) ×ˢ (Γ : Set G)) := hΓ.prod hΓ
    have key := Continuous.ext_on hd (f := fun p : G × G => f (p.1 * p.2))
      (g := fun p : G × G => f p.1 * f p.2)
      (hfc.comp continuous_mul) ((hfc.comp continuous_fst).mul (hfc.comp continuous_snd))
      (by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only
        rw [hval x hx, hval y hy, hval (x * y) (Subgroup.mul_mem _ hx hy), ← map_mul rho]
        rfl)
    intro a b
    exact congrFun key (a, b)
  exact ⟨MonoidHom.mk' f hmul, hfc, fun γ => hval (γ : G) γ.2⟩

/-- **The superrigidity property follows from a uniform-continuity estimate.**

For a dense subgroup `Γ ≤ G` and a complete Hausdorff target, `MargulisSuperrigid Γ Admissible`
reduces to the statement that every admissible homomorphism is uniformly continuous. -/
