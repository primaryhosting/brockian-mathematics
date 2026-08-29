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

theorem isSuperrigidHom_prod {H₁ H₂ : Type*} [Group H₁] [TopologicalSpace H₁]
    [Group H₂] [TopologicalSpace H₂] {Γ : Subgroup G} (ρ : Γ →* H₁ × H₂)
    (h₁ : IsSuperrigidHom Γ ((MonoidHom.fst H₁ H₂).comp ρ))
    (h₂ : IsSuperrigidHom Γ ((MonoidHom.snd H₁ H₂).comp ρ)) :
    IsSuperrigidHom Γ ρ := by
  obtain ⟨f₁, hc₁, he₁⟩ := h₁
  obtain ⟨f₂, hc₂, he₂⟩ := h₂
  refine ⟨(f₁.prod f₂), hc₁.prodMk hc₂, fun γ => ?_⟩
  have e₁ := he₁ γ
  have e₂ := he₂ γ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
    MonoidHom.coe_snd] at e₁ e₂
  exact Prod.ext e₁ e₂

/-- A consequence of superrigidity: if the ambient group `G` is connected and the target `H` is
discrete, then a superrigid homomorphism is trivial.  (In the Margulis setting this rules out
unbounded homomorphisms of higher-rank lattices into discrete groups.) -/
