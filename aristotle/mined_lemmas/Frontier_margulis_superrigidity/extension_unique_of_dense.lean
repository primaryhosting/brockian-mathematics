/-
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring below.)

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

/-!
## Setting

Margulis superrigidity states: if `G` is a semisimple Lie group of real rank at least `2`
(with finite centre and no compact factors), `Γ ≤ G` an irreducible lattice, and
`rho : Γ → H` a homomorphism into a simple Lie group whose image is Zariski dense and
unbounded, then `rho` is the restriction of a *continuous* homomorphism `G → H`.

The conclusion of the theorem is the statement `ExtendsToContinuousHom` below.

Margulis' proof proceeds through the **graph closure**: one forms the closure `Λ` of the
graph `{(γ, rho γ) : γ ∈ Γ}` inside `G × H`, which is a closed subgroup, and the whole
analytic work (boundary maps, higher rank, Zariski density) goes into proving that `Λ`
projects *bijectively* onto `G`, i.e. that `Λ` is the graph of a map. The results below
formalise this reduction: once the graph closure is a graph, superrigidity follows, and
the resulting extension is automatically continuous. We also prove the degenerate base
cases unconditionally.
-/

section Defs

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- `rho : Γ →* H` is the restriction of a continuous homomorphism defined on all of `G`. -/

theorem extension_unique_of_dense [T2Space H]
    (Γ : Subgroup G) (hΓ : Dense (Γ : Set G)) (σ τ : G →* H)
    (hσ : Continuous σ) (hτ : Continuous τ) (h : ∀ γ : Γ, σ (γ : G) = τ (γ : G)) :
    σ = τ := by
  ext g
  refine congrFun (Continuous.ext_on hΓ hσ hτ ?_) g
  rintro x hx
  exact h ⟨x, hx⟩

end Reduction

section BaseCases

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Base case: over a discrete group every homomorphism defined on the whole group
extends (continuously, since every map out of a discrete space is continuous). -/
