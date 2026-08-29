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

set_option grind.warning false

open MeasureTheory

namespace Frontier

/-!
## Overview

Margulis' superrigidity theorem says that a linear representation of an irreducible lattice `Γ`
in a higher-rank semisimple group `G` is, up to passing to a subgroup of finite index, the
restriction of a continuous representation of the ambient group `G`.

This file

* sets up the general notion of *extending a homomorphism defined on a subgroup to a continuous
  homomorphism of the ambient topological group* (`Frontier.ExtendsTo`, `Frontier.Superrigid`,
  `Frontier.VirtuallySuperrigid`);
* records elementary structural facts about this notion (the base case `Frontier.superrigid_top`,
  behaviour under composition and products, uniqueness of extensions, the reduction to the closure
  of the image, and the vanishing of superrigid homomorphisms into abelian targets);
* states Margulis superrigidity for the concrete higher-rank family `SL(n, ℝ)`, `n ≥ 3`, with a
  genuine (polynomial) definition of Zariski density of the image
  (`Frontier.MargulisSuperrigiditySL`);
* proves, as `Frontier.margulis_superrigidity`, the Lean-checked reduction of that statement to
  the statement in which one is allowed first to replace the lattice by an arbitrary subgroup of
  finite index — the standard normalisation step at the start of the proof.

The deep analytic content of Margulis' theorem (the construction of a measurable equivariant map
to a boundary, and its algebraicity) is *not* proved here: it is isolated in the hypothesis of
`Frontier.margulis_superrigidity`.
-/

/-! ## The extension property -/

section Defs

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- `Φ : G →* H` is a continuous extension of the homomorphism `ρ : Γ →* H` defined on the
subgroup `Γ ≤ G`. -/
structure ExtendsTo (Γ : Subgroup G) (ρ : Γ →* H) (Φ : G →* H) : Prop where
  /-- The extension is continuous on the ambient group. -/
  continuous : Continuous Φ
  /-- The extension restricts to `ρ` on `Γ`. -/
  eqOn : ∀ γ : Γ, Φ (γ : G) = ρ γ

/-- The homomorphism `ρ : Γ →* H` is *superrigid*: it extends to a continuous homomorphism
`G →* H`. -/

def IsLatticeInSL {n : ℕ} (Γ : Subgroup (SLR n)) : Prop :=
  letI : MeasurableSpace (SLR n) := borel (SLR n)
  ∃ μ : Measure (SLR n), μ.IsHaarMeasure ∧ IsLatticeIn μ Γ

/-! ## The statement of Margulis superrigidity -/

/-- **Margulis superrigidity for `SL(n, ℝ)`, `n ≥ 3`.**

Let `n ≥ 3`, let `Γ` be a lattice in the higher-rank simple Lie group `G = SL(n, ℝ)`, and let
`ρ : Γ → SL(m, ℝ)` be a homomorphism whose image is Zariski dense.  Then `ρ` agrees with a
continuous representation `G → SL(m, ℝ)` on a subgroup of finite index in `Γ`.

(Since `SL(n, ℝ)` is simple, every lattice in it is automatically irreducible, so no irreducibility
hypothesis is needed; the passage to a finite-index subgroup is the usual one, needed because `ρ`
may be twisted by a finite-order character.) -/
