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

theorem eq_one_of_isSuperrigidHom_of_connected [ConnectedSpace G] [DiscreteTopology H]
    {Γ : Subgroup G} {ρ : Γ →* H} (h : IsSuperrigidHom Γ ρ) : ρ = 1 := by
  obtain ⟨f, hfc, hfe⟩ := h
  have hf1 : ∀ g : G, f g = 1 := by
    intro g
    have hclopen : IsClopen (f ⁻¹' {(1 : H)}) :=
      ⟨(isClosed_discrete _).preimage hfc, (isOpen_discrete _).preimage hfc⟩
    have huniv : f ⁻¹' {(1 : H)} = Set.univ := hclopen.eq_univ ⟨1, by simp⟩
    have : g ∈ f ⁻¹' {(1 : H)} := huniv ▸ Set.mem_univ g
    simpa using this
  ext γ
  simpa [hf1] using (hfe γ).symm

end BaseCase

/-!
## The classical instance: `SL n ℤ ≤ SL n ℝ`

For `n ≥ 3` the group `SL n ℝ` has real rank `n - 1 ≥ 2` and `SL n ℤ` is an irreducible
lattice in it, so Margulis superrigidity applies.  We record the embedding and the induced
statement schema.
-/

section Classical

variable (n : ℕ)

/-- `SL n ℤ`, viewed as a subgroup of `SL n ℝ`. -/
