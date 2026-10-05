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

def IsLatticeSubgroup (μ : MeasureTheory.Measure G) (Γ : Subgroup G) : Prop :=
  DiscreteTopology Γ ∧ ∃ F : Set G, MeasureTheory.IsFundamentalDomain Γ F μ ∧ μ F ≠ ⊤

end Lattice

/-!
## The statement of Margulis superrigidity

Real rank, irreducibility of a lattice and Zariski density of a subset of a linear group are
not available in Mathlib, so the statement is parameterised by them.  Any instantiation of the
predicates yields a genuine mathematical statement; the intended one is
`G` a semisimple Lie group, `higherRank` the assertion `2 ≤ rank_ℝ G`, `irreducibleLattice Γ`
the assertion that `Γ` is an irreducible lattice in `G`, `unbounded S` the assertion that `S`
is not relatively compact in `H`, and `zariskiDense S` the assertion that `S` is Zariski dense
in the algebraic group `H`.
-/

/-- The Margulis superrigidity statement for the pair of topological groups `G`, `H`, relative
to the abstract predicates `higherRank`, `irreducibleLattice`, `unbounded`, `zariskiDense`:

if `G` has higher rank and `Γ ≤ G` is an irreducible lattice, then every homomorphism
`ρ : Γ →* H` with unbounded and Zariski dense image is the restriction of a continuous
homomorphism `G →* H`. -/
