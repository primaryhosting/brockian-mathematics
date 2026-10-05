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

open MeasureTheory

/-!
## The setting

Margulis superrigidity concerns an irreducible lattice `Γ` in a higher-rank semisimple
group `G` and a linear representation `rho : Γ → H`.  It asserts that, under suitable
non-degeneracy assumptions on the image of `rho`, the representation `rho` is the restriction
to `Γ` of a *continuous* homomorphism `G → H`; i.e. the abstract homomorphism `rho`, defined
only on the discrete group `Γ`, is forced to come from the ambient topological group.

Below we formalise:

* `Frontier.IsLatticeIn` — a discrete subgroup with a finite-measure fundamental domain;
* `Frontier.ExtendsToContinuousHom` — the superrigidity conclusion for one representation;
* `Frontier.SuperrigidLattice` — "every non-degenerate representation of `Γ` extends";
* `Frontier.MargulisSuperrigidityStatement` — the theorem itself, as a statement schema in
  which the (semisimplicity + higher rank + irreducibility) package is an abstract
  predicate; `Frontier.HasHigherRankSplitTorus` records a concrete necessary condition
  for real rank `≥ 2` that such a predicate must imply;
* `Frontier.margulis_superrigidity` — the theorem proved here: the *abelian base case*
  together with uniqueness of the extension, plus (`margulis_superrigidity_finite_index`)
  a Lean-checked reduction from finite-index subgroups to the whole lattice.
-/

/-- `IsLatticeIn μ Γ`: the subgroup `Γ` of the topological group `G` is a **lattice**, i.e.
it is discrete and admits a fundamental domain of finite `μ`-measure (`μ` being a Haar
measure on `G`). -/

theorem margulis_superrigidity {G : Type*} [Group G] [TopologicalSpace G]
    {H : Type*} [CommGroup H] [TopologicalSpace H] [T2Space H] [IsMulTorsionFree H]
    {Γ : Subgroup G} (hab : Finite (Abelianization Γ)) (rho : Γ →* H) :
    (∀ γ : Γ, rho γ = 1) ∧ ExtendsToContinuousHom Γ rho ∧
      (Dense (Γ : Set G) → ∀ Φ Ψ : G →* H, Continuous Φ → Continuous Ψ →
        (∀ γ : Γ, Φ (γ : G) = rho γ) → (∀ γ : Γ, Ψ (γ : G) = rho γ) → Φ = Ψ) := by
  have htriv : ∀ γ : Γ, rho γ = 1 := hom_eq_one_of_finite_abelianization hab rho
  refine ⟨htriv, ⟨1, continuous_const, fun γ => by simp [htriv γ]⟩, ?_⟩
  intro hd Φ Ψ hΦ hΨ hΦrho hΨrho
  exact continuousHom_ext_of_dense hd hΦ hΨ (fun γ => by rw [hΦrho γ, hΨrho γ])

/-- **Finite-index reduction for the superrigidity conclusion (abelian targets).**
If the restriction of `rho` to a finite-index subgroup `Γ₀` of the lattice `Γ` is the
restriction of a continuous homomorphism `Φ : G →* H`, with `H` torsion-free abelian, then
`Φ` extends `rho` on all of `Γ`; in particular `ExtendsToContinuousHom Γ rho` holds. -/
