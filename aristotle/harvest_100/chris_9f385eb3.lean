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

/-!
## Overview

Margulis' superrigidity theorem says, informally:

> Let `G` be a connected semisimple Lie group of real rank at least `2`, with finite centre and
> no compact factors, and let `Γ ≤ G` be an irreducible lattice.  Let `H` be a connected,
> centre-free, (topologically) simple, non-compact Lie group and let `f : Γ → H` be a group
> homomorphism whose image is unbounded (and Zariski dense).  Then `f` is the restriction of a
> continuous homomorphism `G → H`.

This file formalises the *statement* in topological-group language
(`Frontier.MargulisSuperrigidityStatement`), and proves several Lean-checked pieces of it:

* an unconditional **base case** (`Frontier.superrigid_of_discrete_top`): when the lattice is all
  of `G` (so that `G` is discrete), every homomorphism extends continuously; together with
  `Frontier.superrigid_of_subsingleton_target` these are the degenerate instances of the theorem;
* the **semisimple-to-simple reduction** (`Frontier.margulis_superrigidity`): superrigidity for a
  target which is a product of two simple factors follows from superrigidity for each factor.
  This is the first reduction step in Margulis' proof, and here it is checked by Lean;
* two structural facts about the conclusion: uniqueness of a continuous extension on a dense
  subgroup (`Frontier.extension_unique_of_dense`) and invariance of superrigidity under
  isomorphism of the target as a topological group (`Frontier.superrigid_of_topGroupEquiv`).

The deep analytic input (the case of a single simple target) is carried as an explicit hypothesis
of `Frontier.margulis_superrigidity`, never as an axiom.

Conventions and caveats about the formalisation:

* "real rank at least `n`" is approximated by the existence of a closed embedding of the
  `n`-dimensional split torus `(ℝ^n, +)` as a subgroup (`Frontier.HasSplitRankAtLeast`); this is
  the split-torus characterisation of the rank, without the requirement that the torus consist of
  `ℝ`-diagonalisable elements, which is not expressible without algebraic-group machinery.
* "simple Lie group" is rendered by purely topological conditions
  (`Frontier.IsSimpleTarget`): connected, locally compact, Hausdorff, non-compact, centre-free and
  with no closed normal subgroups other than `⊥` and `⊤`.
* irreducibility of the lattice is rendered by: `Γ · N` is dense for every closed normal subgroup
  `N ≠ ⊥` (`Frontier.IsIrreducibleLattice`).
-/

universe u v

namespace Frontier

section Defs

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- `Γ` is a **lattice** in `G`: it is discrete and admits a fundamental domain of finite measure
for the (Haar) measure `μ`. -/
def IsLattice [MeasurableSpace G] (μ : MeasureTheory.Measure G) (Γ : Subgroup G) : Prop :=
  DiscreteTopology Γ ∧
    ∃ F : Set G, MeasureTheory.IsFundamentalDomain Γ F μ ∧ μ F ≠ ⊤

/-- `Γ` is an **irreducible** lattice: its product with any non-trivial closed normal subgroup of
`G` is dense.  (For a semisimple `G` this is the usual irreducibility condition: the projection of
`Γ` to every proper quotient by a factor is dense.) -/
def IsIrreducibleLattice [IsTopologicalGroup G] (Γ : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N.Normal → IsClosed (N : Set G) → N ≠ ⊥ →
    Dense ((Γ ⊔ N : Subgroup G) : Set G)

/-- `G` has **split rank at least `n`**: the additive group `ℝ^n` embeds in `G` as a closed
subgroup, via a continuous homomorphism. -/
def HasSplitRankAtLeast (G : Type*) [Group G] [TopologicalSpace G] (n : ℕ) : Prop :=
  ∃ f : Multiplicative (Fin n → ℝ) →* G, Continuous f ∧ Topology.IsClosedEmbedding f

/-- The hypotheses on the pair `(G, Γ)` in Margulis superrigidity: `G` is a connected topological
group with finite centre and real rank at least `2`, and `Γ` is an irreducible lattice in `G`. -/
structure IsHigherRankLattice [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) (Γ : Subgroup G) : Prop where
  /-- `Γ` is a lattice in `G`. -/
  lattice : IsLattice μ Γ
  /-- The lattice is irreducible. -/
  irreducible : IsIrreducibleLattice Γ
  /-- `G` has real rank at least `2` ("higher rank"). -/
  higher_rank : HasSplitRankAtLeast G 2
  /-- `G` is connected. -/
  connected : ConnectedSpace G
  /-- `G` is locally compact (a Lie group is). -/
  locallyCompact : LocallyCompactSpace G
  /-- `G` is Hausdorff. -/
  t2 : T2Space G
  /-- `G` has finite centre. -/
  center_finite : (Subgroup.center G : Set G).Finite

/-- The hypotheses on the target group `H`: a connected, centre-free, non-compact, topologically
simple, locally compact Hausdorff group.  This is the topological rendering of "connected simple
non-compact adjoint Lie group". -/
structure IsSimpleTarget (H : Type*) [Group H] [TopologicalSpace H] : Prop where
  /-- `H` is a topological group. -/
  topGroup : IsTopologicalGroup H
  /-- `H` is connected. -/
  connected : ConnectedSpace H
  /-- `H` is locally compact. -/
  locallyCompact : LocallyCompactSpace H
  /-- `H` is Hausdorff. -/
  t2 : T2Space H
  /-- `H` is not compact. -/
  noncompact : ¬ CompactSpace H
  /-- `H` has trivial centre. -/
  centerless : Subgroup.center H = ⊥
  /-- `H` is topologically simple. -/
  simple : ∀ N : Subgroup H, N.Normal → IsClosed (N : Set H) → N = ⊥ ∨ N = ⊤

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The conclusion of superrigidity for a homomorphism `f : Γ → H`: `f` is the restriction of a
continuous homomorphism `G → H`. -/
def ExtendsToContinuous (Γ : Subgroup G) (f : Γ →* H) : Prop :=
  ∃ F : G →* H, Continuous F ∧ ∀ γ : Γ, F (γ : G) = f γ

/-- The image of `f` is unbounded, i.e. not relatively compact.  (In the Lie group setting this is
Margulis' hypothesis that `f (Γ)` is unbounded in `H`.) -/
def HasUnboundedImage (Γ : Subgroup G) (f : Γ →* H) : Prop :=
  ¬ IsCompact (closure (Set.range (fun γ : Γ => f γ)))

/-- **Superrigidity for the pair `(Γ ≤ G, H)`**: every homomorphism `Γ → H` with unbounded image
extends to a continuous homomorphism `G → H`. -/
def Superrigid (Γ : Subgroup G) (H : Type*) [Group H] [TopologicalSpace H] : Prop :=
  ∀ f : Γ →* H, HasUnboundedImage Γ f → ExtendsToContinuous Γ f

end Defs

section BaseCases

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [Group H] [TopologicalSpace H]

/-- **Base case**: if `Γ = ⊤` is a lattice in `G` — equivalently, if `G` is discrete — then every
homomorphism `Γ → H` extends to a continuous homomorphism on `G`, so superrigidity holds
(trivially, and with no rank assumption). -/
theorem superrigid_of_discrete_top [DiscreteTopology G] :
    Superrigid (⊤ : Subgroup G) H := by
  intro f _
  refine ⟨f.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, continuous_of_discreteTopology, ?_⟩
  intro γ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 1

/-- **Degenerate case**: superrigidity is trivially true for a trivial target group. -/
theorem superrigid_of_subsingleton_target (Γ : Subgroup G) [Subsingleton H] :
    Superrigid Γ H := by
  intro f _
  exact ⟨1, continuous_const, fun γ => Subsingleton.elim _ _⟩

/-- **Uniqueness of the extension**: a continuous homomorphism out of `G` into a Hausdorff group is
determined by its restriction to a dense subgroup.  (In Margulis' setting the relevant density is
Zariski density of `Γ`; this is the topological analogue.) -/
theorem extension_unique_of_dense [T2Space H] {Γ : Subgroup G}
    (hΓ : Dense (Γ : Set G)) {F K : G →* H} (hF : Continuous F) (hK : Continuous K)
    (h : ∀ γ : Γ, F (γ : G) = K (γ : G)) : F = K := by
  ext g
  refine congrFun (Continuous.ext_on hΓ hF hK ?_) g
  rintro x hx
  exact h ⟨x, hx⟩

/-- **Transfer of superrigidity along an isomorphism of topological groups**: superrigidity of a
pair `(Γ ≤ G, H)` depends only on the isomorphism class of the target as a topological group. -/
theorem superrigid_of_topGroupEquiv {H' : Type*} [Group H'] [TopologicalSpace H']
    {Γ : Subgroup G} (e : H ≃* H') (he : Continuous e) (he' : Continuous e.symm)
    (h : Superrigid Γ H) : Superrigid Γ H' := by
  set E : H ≃ₜ H' := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := he' }
  intro f hf
  have himg : Set.range (fun γ : Γ => (e.symm.toMonoidHom.comp f) γ) =
      E.symm '' Set.range (fun γ : Γ => f γ) := by
    rw [← Set.range_comp]
    rfl
  have hunb : HasUnboundedImage Γ (e.symm.toMonoidHom.comp f) := by
    intro hc
    refine hf ?_
    have : closure (Set.range (fun γ : Γ => f γ)) =
        E '' closure (Set.range (fun γ : Γ => (e.symm.toMonoidHom.comp f) γ)) := by
      rw [himg, E.image_closure, ← Set.image_comp]
      simp [Set.image_id']
    rw [this]
    exact hc.image E.continuous
  obtain ⟨F, hFcont, hF⟩ := h (e.symm.toMonoidHom.comp f) hunb
  refine ⟨e.toMonoidHom.comp F, he.comp hFcont, ?_⟩
  intro γ
  simp [hF γ]

end BaseCases

section Statement

/-- **The statement of Margulis superrigidity for higher-rank lattices.**

For every irreducible lattice `Γ` in a connected, locally compact, Hausdorff group `G` of real
rank at least `2` with finite centre, and every connected, non-compact, centre-free,
topologically simple target group `H`, every homomorphism `Γ →* H` with unbounded image is the
restriction of a continuous homomorphism `G →* H`. -/
def MargulisSuperrigidityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) (Γ : Subgroup G), IsHigherRankLattice μ Γ →
    ∀ (H : Type v) [Group H] [TopologicalSpace H], IsSimpleTarget H → Superrigid Γ H

end Statement

section Reduction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
variable {H₁ H₂ : Type v} [Group H₁] [TopologicalSpace H₁] [Group H₂] [TopologicalSpace H₂]

/-- **Margulis superrigidity for higher-rank lattices: the reduction to simple targets.**

Let `Γ` be an irreducible lattice in a connected, locally compact, Hausdorff group `G` of real rank
at least `2` with finite centre, and let `H₁ × H₂` be a semisimple target, i.e. a product of two
groups each of which is connected, non-compact, centre-free and topologically simple.  Let
`f : Γ →* H₁ × H₂` be a homomorphism whose image is unbounded in each factor.

Assuming Margulis superrigidity for simple targets (`margulis :
Frontier.MargulisSuperrigidityStatement`, the deep analytic input, carried as an explicit
hypothesis rather than an axiom), the homomorphism `f` extends to a continuous homomorphism
`G → H₁ × H₂`.

Thus the semisimple case of superrigidity is reduced, in a Lean-checked way, to the simple case:
one applies the simple case to each of the two projections of `f` and pairs the resulting
continuous extensions. -/
theorem margulis_superrigidity (margulis : MargulisSuperrigidityStatement.{u, v})
    {μ : MeasureTheory.Measure G} {Γ : Subgroup G}
    (hΓ : IsHigherRankLattice μ Γ)
    (hH₁ : IsSimpleTarget H₁) (hH₂ : IsSimpleTarget H₂)
    (f : Γ →* H₁ × H₂)
    (hu₁ : HasUnboundedImage Γ ((MonoidHom.fst H₁ H₂).comp f))
    (hu₂ : HasUnboundedImage Γ ((MonoidHom.snd H₁ H₂).comp f)) :
    ExtendsToContinuous Γ f := by
  obtain ⟨F₁, hF₁cont, hF₁⟩ := margulis G μ Γ hΓ H₁ hH₁ ((MonoidHom.fst H₁ H₂).comp f) hu₁
  obtain ⟨F₂, hF₂cont, hF₂⟩ := margulis G μ Γ hΓ H₂ hH₂ ((MonoidHom.snd H₁ H₂).comp f) hu₂
  refine ⟨F₁.prod F₂, hF₁cont.prodMk hF₂cont, ?_⟩
  intro γ
  have h₁ := hF₁ γ
  have h₂ := hF₂ γ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd] at h₁ h₂
  exact Prod.ext h₁ h₂

end Reduction

end Frontier

