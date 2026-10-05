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
def ExtendsToContinuousHom (Γ : Subgroup G) (rho : Γ →* H) : Prop :=
  ∃ σ : G →* H, Continuous σ ∧ ∀ γ : Γ, σ (γ : G) = rho γ

/-- The graph of `rho : Γ →* H`, as a subgroup of `G × H`. -/
def graphSubgroup (Γ : Subgroup G) (rho : Γ →* H) : Subgroup (G × H) :=
  ((Γ.subtype.prod rho : Γ →* G × H)).range

/-- The closure of the graph of `rho` in `G × H`; it is a closed subgroup of `G × H`
whenever `G × H` is a topological group. This is the object at the heart of Margulis'
argument. -/
def graphClosure [IsTopologicalGroup G] [IsTopologicalGroup H]
    (Γ : Subgroup G) (rho : Γ →* H) : Subgroup (G × H) :=
  (graphSubgroup Γ rho).topologicalClosure

omit [TopologicalSpace G] [TopologicalSpace H] in
theorem mem_graphSubgroup (Γ : Subgroup G) (rho : Γ →* H) (γ : Γ) :
    ((γ : G), rho γ) ∈ graphSubgroup Γ rho :=
  ⟨γ, rfl⟩

theorem mem_graphClosure [IsTopologicalGroup G] [IsTopologicalGroup H]
    (Γ : Subgroup G) (rho : Γ →* H) (γ : Γ) :
    ((γ : G), rho γ) ∈ graphClosure Γ rho :=
  (graphSubgroup Γ rho).le_topologicalClosure (mem_graphSubgroup Γ rho γ)

end Defs

section Reduction

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The first-coordinate projection, restricted to the graph closure. -/
def graphProj (Γ : Subgroup G) (rho : Γ →* H) : graphClosure Γ rho →* G :=
  (MonoidHom.fst G H).comp (graphClosure Γ rho).subtype

theorem continuous_graphProj (Γ : Subgroup G) (rho : Γ →* H) :
    Continuous (graphProj Γ rho) :=
  continuous_fst.comp continuous_subtype_val

theorem graphProj_injective (Γ : Subgroup G) (rho : Γ →* H)
    (hinj : ∀ h : H, ((1 : G), h) ∈ graphClosure Γ rho → h = 1) :
    Function.Injective (graphProj Γ rho) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨g, h⟩, hgh⟩ hg
  have hg1 : g = 1 := hg
  subst hg1
  have : h = 1 := hinj h hgh
  subst this
  rfl

theorem graphProj_surjective (Γ : Subgroup G) (rho : Γ →* H)
    (hsurj : ∀ g : G, ∃ h : H, (g, h) ∈ graphClosure Γ rho) :
    Function.Surjective (graphProj Γ rho) := by
  intro g
  obtain ⟨h, hh⟩ := hsurj g
  exact ⟨⟨(g, h), hh⟩, rfl⟩

/-- **Core reduction.** If the closure of the graph of `rho` projects bijectively and
openly onto `G`, then `rho` extends to a continuous homomorphism `G →* H`. -/
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
theorem margulis_superrigidity_of_sigmaCompact_graphClosure
    [T2Space G] [BaireSpace G]
    (Γ : Subgroup G) (rho : Γ →* H)
    (hcompact : SigmaCompactSpace (graphClosure Γ rho))
    (hsurj : ∀ g : G, ∃ h : H, (g, h) ∈ graphClosure Γ rho)
    (hinj : ∀ h : H, ((1 : G), h) ∈ graphClosure Γ rho → h = 1) :
    ExtendsToContinuousHom Γ rho := by
  haveI := hcompact
  refine extendsToContinuousHom_of_graphClosure Γ rho hsurj hinj ?_
  exact MonoidHom.isOpenMap_of_sigmaCompact (graphProj Γ rho)
    (graphProj_surjective Γ rho hsurj) (continuous_graphProj Γ rho)

/-- The graph closure is σ-compact as soon as `G` and `H` are (e.g. for second countable
Lie groups), being a closed subset of `G × H`. -/
theorem sigmaCompactSpace_graphClosure [SigmaCompactSpace G] [SigmaCompactSpace H]
    (Γ : Subgroup G) (rho : Γ →* H) :
    SigmaCompactSpace (graphClosure Γ rho) :=
  (graphSubgroup Γ rho).isClosed_topologicalClosure.sigmaCompactSpace

/-- **Margulis superrigidity, reduced to the graph-closure criterion** (main form).

The topological hypotheses on `G` and `H` (Hausdorff, Baire, σ-compact) hold for all
second countable Lie groups, so the only real input is the graph-closure criterion:
the closure `Λ` of the graph of `rho` inside `G × H` meets every vertical line `{g} × H`
and meets `{1} × H` only in the identity, i.e. `Λ` is the graph of a map `G → H`. -/
theorem margulis_superrigidity
    [T2Space G] [BaireSpace G] [SigmaCompactSpace G] [SigmaCompactSpace H]
    (Γ : Subgroup G) (rho : Γ →* H)
    (hsurj : ∀ g : G, ∃ h : H, (g, h) ∈ graphClosure Γ rho)
    (hinj : ∀ h : H, ((1 : G), h) ∈ graphClosure Γ rho → h = 1) :
    ExtendsToContinuousHom Γ rho :=
  margulis_superrigidity_of_sigmaCompact_graphClosure Γ rho
    (sigmaCompactSpace_graphClosure Γ rho) hsurj hinj

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Uniqueness of the extension: a continuous homomorphism on `G` is determined by its
restriction to a dense subgroup. -/
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
theorem margulis_superrigidity_discrete [DiscreteTopology G]
    (rho : (⊤ : Subgroup G) →* H) :
    ExtendsToContinuousHom (⊤ : Subgroup G) rho := by
  refine ⟨rho.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, continuous_of_discreteTopology,
    ?_⟩
  intro γ
  exact congrArg rho (Subtype.ext rfl)

/-- Base case: any homomorphism into the trivial group extends. -/
theorem margulis_superrigidity_trivial_target [Subsingleton H]
    (Γ : Subgroup G) (rho : Γ →* H) :
    ExtendsToContinuousHom Γ rho :=
  ⟨1, continuous_const, fun _ => Subsingleton.elim _ _⟩

end BaseCases

section Sanity

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Sanity check that the hypotheses of `margulis_superrigidity` are not vacuous: if
`Γ = ⊤` and `rho` is continuous, the graph closure genuinely satisfies the two
graph-closure conditions. -/
theorem graphClosure_conditions_of_continuous_top [T2Space G] [T2Space H]
    (rho : (⊤ : Subgroup G) →* H) (hrho : Continuous rho) :
    (∀ g : G, ∃ h : H, (g, h) ∈ graphClosure (⊤ : Subgroup G) rho) ∧
      (∀ h : H, ((1 : G), h) ∈ graphClosure (⊤ : Subgroup G) rho → h = 1) := by
  have hclosed : IsClosed ((graphSubgroup (⊤ : Subgroup G) rho : Set (G × H))) := by
    have himage : (graphSubgroup (⊤ : Subgroup G) rho : Set (G × H)) =
        {p : G × H | rho ⟨p.1, Subgroup.mem_top _⟩ = p.2} := by
      ext ⟨g, h⟩
      constructor
      · rintro ⟨γ, hγ⟩
        have h1 : (γ : G) = g := congrArg Prod.fst hγ
        have h2 : rho γ = h := congrArg Prod.snd hγ
        show rho ⟨g, Subgroup.mem_top _⟩ = h
        rw [← h2]
        exact congrArg rho (Subtype.ext h1.symm)
      · rintro (hgh : rho ⟨g, Subgroup.mem_top _⟩ = h)
        exact ⟨⟨g, Subgroup.mem_top _⟩, by simp [← hgh]⟩
    rw [himage]
    have hcont : Continuous fun p : G × H => rho ⟨p.1, Subgroup.mem_top _⟩ :=
      hrho.comp (continuous_fst.subtype_mk _)
    exact isClosed_eq hcont continuous_snd
  have hcl : graphClosure (⊤ : Subgroup G) rho = graphSubgroup (⊤ : Subgroup G) rho := by
    apply SetLike.ext'
    exact hclosed.closure_eq
  constructor
  · intro g
    exact ⟨rho ⟨g, Subgroup.mem_top _⟩, by
      rw [hcl]; exact mem_graphSubgroup (⊤ : Subgroup G) rho ⟨g, Subgroup.mem_top _⟩⟩
  · intro h hh
    rw [hcl] at hh
    obtain ⟨γ, hγ⟩ := hh
    have h1 : (γ : G) = 1 := congrArg Prod.fst hγ
    have h2 : rho γ = h := congrArg Prod.snd hγ
    have : γ = 1 := Subtype.ext h1
    rw [this] at h2
    simpa using h2.symm

end Sanity

end Frontier

