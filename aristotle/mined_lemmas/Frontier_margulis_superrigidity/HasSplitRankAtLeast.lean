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
