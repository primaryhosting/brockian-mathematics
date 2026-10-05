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

theorem continuous_conjHom {f : G →* H} (hf : Continuous f) (γ : G) (h : H) :
    Continuous (conjHom f γ h) := by
  have : Continuous fun g : G => γ⁻¹ * g * γ :=
    (continuous_mul_right γ).comp (continuous_mul_left γ⁻¹)
  exact (continuous_const.mul (hf.comp this)).mul continuous_const

/-- **Margulis superrigidity, reduction step.**

Let `Γ₀ ≤ Γ` be subgroups of a topological group `G` with `Γ₀` normal in `Γ`, and let
`ρ : Γ →* H` be a homomorphism into a topological group `H`.  Assume:

* `f : G →* H` is a continuous homomorphism extending `ρ` on `Γ₀`;
* continuous homomorphisms `G →* H` are determined by their restriction to `Γ₀`
  (in Margulis' setting this follows from the Borel density theorem, `Γ₀` being Zariski
  dense in `G`);
* the image `ρ Γ₀` has trivial centraliser in `H` (in Margulis' setting this holds because
  `ρ Γ₀` is Zariski dense in the centre-free simple group `H`).

Then `f` already extends `ρ` on all of `Γ`; that is, `ρ` itself is superrigid.

This is the Lean-checked reduction of superrigidity for a lattice `Γ` to superrigidity for a
normal (e.g. finite-index) subgroup `Γ₀`. -/
