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

theorem Superrigid.eq_one_of_commGroup {A : Type*} [CommGroup A] [TopologicalSpace A]
    {Γ : Subgroup G} {ρ : Γ →* A} (h : Superrigid Γ ρ) (hG : commutator G = ⊤) : ρ = 1 := by
  obtain ⟨Φ, _, hΦe⟩ := h
  have hker : commutator G ≤ Φ.ker := by
    rw [commutator_eq_closure]
    refine Subgroup.closure_le _ |>.2 ?_
    rintro x ⟨a, b, rfl⟩
    simp [MonoidHom.mem_ker, commutatorElement_def]
  ext γ
  have : Φ (γ : G) = 1 := hker (hG ▸ Subgroup.mem_top _)
  simpa [hΦe γ] using this

end Structural

/-! ## Lattices -/

/-- `Γ` is a *lattice* in the topological group `G` with respect to the (Haar) measure `μ`: it is
a discrete subgroup admitting a fundamental domain of finite measure. -/
structure IsLatticeIn {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) (Γ : Subgroup G) : Prop where
  /-- A lattice is a discrete subgroup. -/
  discrete : DiscreteTopology Γ
  /-- A lattice has a fundamental domain of finite volume. -/
  finite_covolume : ∃ F : Set G, IsFundamentalDomain Γ F μ ∧ μ F < ⊤

/-! ## The higher-rank groups `SL(n, ℝ)` and Zariski density -/

/-- The special linear group `SL(n, ℝ)`.  For `n ≥ 3` this is a connected simple Lie group of real
rank `n - 1 ≥ 2`, the basic example to which Margulis superrigidity applies. -/
abbrev SLR (n : ℕ) : Type := Matrix.SpecialLinearGroup (Fin n) ℝ

/-- The tuple of matrix entries of an element of `SL(m, ℝ)`, i.e. its coordinates as a point of
the affine space in which the algebraic group `SL_m` sits. -/
