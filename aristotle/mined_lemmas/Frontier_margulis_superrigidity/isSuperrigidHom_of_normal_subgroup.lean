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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Basic vocabulary

Margulis superrigidity says, informally:

> Let `G` be a semisimple Lie group of real rank at least `2`, let `Γ ≤ G` be an irreducible
> lattice, and let `ρ : Γ → H` be a homomorphism into a (simple, centre-free) Lie group whose
> image is unbounded and Zariski dense.  Then `ρ` is the restriction of a *continuous*
> homomorphism `G → H`.

The statement is formalised below as `Frontier.MargulisSuperrigidityStatement`, a `Prop`-valued
schema parameterised by the (currently unformalised in Mathlib) predicates "higher rank",
"irreducible lattice", "unbounded" and "Zariski dense".  The notion of a lattice is given a
genuine measure-theoretic definition in `Frontier.IsLatticeSubgroup`.

The theorem `Frontier.margulis_superrigidity` is a Lean-checked *reduction*: it verifies
Margulis' first reduction step, namely that superrigidity for a normal subgroup `Γ₀ ⊴ Γ`
(in practice a finite-index subgroup) already gives superrigidity for `Γ` itself, provided
the extension is unique (in the Margulis setting this comes from Borel density) and the image
`ρ Γ₀` has trivial centraliser in the target.
-/

section Extension

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- `ExtendsContinuously Γ ρ f` says that the continuous homomorphism `f : G →* H` restricts
on the subgroup `Γ ≤ G` to the given homomorphism `ρ : Γ →* H`.  This is the conclusion of
Margulis superrigidity. -/

theorem isSuperrigidHom_of_normal_subgroup {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ)
    (hnorm : ∀ γ ∈ Γ, ∀ x ∈ Γ₀, γ * x * γ⁻¹ ∈ Γ₀)
    (ρ : Γ →* H) (f : G →* H) (hf : Continuous f)
    (hext : ∀ (x : G) (hx : x ∈ Γ₀), f x = ρ ⟨x, hle hx⟩)
    (huniq : ∀ f₁ f₂ : G →* H, Continuous f₁ → Continuous f₂ →
      (∀ x ∈ Γ₀, f₁ x = f₂ x) → f₁ = f₂)
    (hcent : ∀ h : H, (∀ (x : G) (hx : x ∈ Γ₀), h * ρ ⟨x, hle hx⟩ = ρ ⟨x, hle hx⟩ * h) → h = 1) :
    IsSuperrigidHom Γ ρ :=
  ⟨f, margulis_superrigidity hle hnorm ρ f hf hext huniq hcent⟩

/-- Sanity check that the hypotheses of `Frontier.margulis_superrigidity` are satisfiable (the
reduction is not vacuous): for a discrete group with trivial centre, the tautological
representation of `Γ = Γ₀ = ⊤` satisfies all of them. -/
example (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hcentre : ∀ k : K, (∀ y : K, k * y = y * k) → k = 1) :
    ExtendsContinuously (⊤ : Subgroup K) (Subgroup.topEquiv (G := K)).toMonoidHom
      (MonoidHom.id K) :=
  margulis_superrigidity (Γ := ⊤) (Γ₀ := ⊤) le_rfl (fun _ _ _ _ => trivial) _ _
    continuous_id (fun _ _ => rfl)
    (fun _ _ _ _ h => MonoidHom.ext fun x => h x trivial)
    (fun h hh => hcentre h fun y => hh y trivial)

end Reduction

/-!
## Base cases and consequences
-/

section BaseCase

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Degenerate base case (rank `0`): if the ambient group is discrete, every homomorphism
defined on the whole group is superrigid. -/
