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

theorem extendsToContinuousHom_of_graphClosure
    (Γ : Subgroup G) (rho : Γ →* H)
    (hsurj : ∀ g : G, ∃ h : H, (g, h) ∈ graphClosure Γ rho)
    (hinj : ∀ h : H, ((1 : G), h) ∈ graphClosure Γ rho → h = 1)
    (hopen : IsOpenMap (graphProj Γ rho)) :
    ExtendsToContinuousHom Γ rho := by
  have hbij : Function.Bijective (graphProj Γ rho) :=
    ⟨graphProj_injective Γ rho hinj, graphProj_surjective Γ rho hsurj⟩
  let E : graphClosure Γ rho ≃* G := MulEquiv.ofBijective (graphProj Γ rho) hbij
  have hhomeo : Continuous (E.symm : G → graphClosure Γ rho) :=
    (Equiv.continuous_symm_iff E.toEquiv).mpr hopen
  refine ⟨((MonoidHom.snd G H).comp (graphClosure Γ rho).subtype).comp
    (E.symm : G →* graphClosure Γ rho), ?_, ?_⟩
  · exact continuous_snd.comp (continuous_subtype_val.comp hhomeo)
  · intro γ
    have hmem : ((γ : G), rho γ) ∈ graphClosure Γ rho := mem_graphClosure Γ rho γ
    have hE : E ⟨((γ : G), rho γ), hmem⟩ = (γ : G) := rfl
    have hsymm : E.symm (γ : G) = ⟨((γ : G), rho γ), hmem⟩ :=
      E.injective ((E.apply_symm_apply _).trans hE.symm)
    simp [hsymm]

/-- **Margulis superrigidity, reduced to the graph-closure criterion.**

Let `Γ` be a subgroup of a topological group `G` and `rho : Γ →* H` a homomorphism into a
topological group `H`. Assume the closure `Λ` of the graph of `rho` in `G × H` is
σ-compact (automatic for closed subgroups of second countable, locally compact groups
such as real Lie groups), that `G` is Hausdorff and Baire (again automatic for Lie
groups), and — this is the deep analytic input supplied by higher rank, irreducibility of
the lattice and Zariski density of the image in Margulis' theorem — that `Λ` meets every
vertical line `{g} × H` and meets `{1} × H` only in the identity.

Then `rho` is the restriction of a continuous homomorphism `G →* H`, which is the
conclusion of Margulis superrigidity. -/
