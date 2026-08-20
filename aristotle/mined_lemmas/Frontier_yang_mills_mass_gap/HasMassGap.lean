/- (Lean requires `import` to be the first command, so this header is a block comment.)
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology

namespace Frontier

/-!
## Framework

The Clay Millennium Problem asks for the construction of a quantum Yang–Mills theory
on `ℝ⁴` with a compact simple gauge group, satisfying the Wightman axioms, and having a
positive *mass gap*: the spectrum of the Hamiltonian consists of the vacuum energy `0`
together with a set bounded below by some `Δ > 0`.

Below we
* formalise the notion of a mass gap for an energy spectrum (`Frontier.HasMassGap`),
* formalise an abstract quantum theory carrying the structural data required by the
  problem (`Frontier.QuantumTheory`): a complex Hilbert space, a normalised vacuum,
  a unitary representation of the translation group of `ℝ⁴` fixing the vacuum,
  a unitary action of the gauge group fixing the vacuum, and a closed, non-negative
  energy spectrum containing the vacuum energy `0`,
* state the existence-and-mass-gap conjecture relative to a predicate `IsYangMills`
  singling out the quantum Yang–Mills theories (`Frontier.YangMillsMassGap`), and
* prove a *Lean-checked reduction* (`Frontier.yang_mills_mass_gap`): if a Yang–Mills
  theory arises as a continuum limit of regularisations (e.g. lattice gauge theories)
  whose mass gaps are bounded below by a **uniform** `Δ > 0`, then the conjecture holds.
  This is the standard shape of the constructive strategy: the hard analytic input is a
  uniform-in-the-cutoff spectral gap, and the passage to the limit is what is verified here.

No unproved axioms are introduced: the conjecture itself is *stated*, and what is *proved*
is the reduction, together with the base case of a free massive theory.
-/

/-- `HasMassGap spec Δ` says that the energy spectrum `spec` has a mass gap of size `Δ`:
`Δ` is positive, the vacuum energy `0` belongs to the spectrum, and every other point of
the spectrum is at least `Δ`. -/

def HasMassGap (spec : Set ℝ) (Δ : ℝ) : Prop :=
  0 < Δ ∧ (0 : ℝ) ∈ spec ∧ ∀ E ∈ spec, E = 0 ∨ Δ ≤ E

/-- The structural data of a quantum field theory on `ℝ⁴` in the Wightman framework, at the
level of generality needed to state the mass gap problem: a complex Hilbert space of states,
a normalised vacuum vector, a unitary representation of the spacetime translation group
`ℝ⁴` leaving the vacuum invariant, a unitary action of the (compact, simple) gauge group
leaving the vacuum invariant, and the spectrum of the Hamiltonian, which is closed,
contained in `[0, ∞)` (positivity of the energy) and contains the vacuum energy `0`. -/
structure QuantumTheory where
  /-- The Hilbert space of states. -/
  Space : Type
  [normedAddCommGroup : NormedAddCommGroup Space]
  [innerProductSpace : InnerProductSpace ℂ Space]
  [completeSpace : CompleteSpace Space]
  /-- The vacuum state. -/
  vacuum : Space
  /-- The vacuum is a unit vector. -/
  vacuum_norm : ‖vacuum‖ = 1
  /-- The unitary representation of the spacetime translation group `ℝ⁴`. -/
  translation : (Fin 4 → ℝ) → (Space ≃ₗᵢ[ℂ] Space)
  translation_zero : translation 0 = LinearIsometryEquiv.refl ℂ Space
  translation_add : ∀ a b, translation (a + b) = (translation b).trans (translation a)
  translation_vacuum : ∀ a, translation a vacuum = vacuum
  /-- The gauge group. -/
  gaugeGroup : Type
  [gaugeGroupGroup : Group gaugeGroup]
  /-- The unitary action of the gauge group on the states. -/
  gaugeAction : gaugeGroup → (Space ≃ₗᵢ[ℂ] Space)
  gaugeAction_one : gaugeAction 1 = LinearIsometryEquiv.refl ℂ Space
  gaugeAction_mul : ∀ g h, gaugeAction (g * h) = (gaugeAction h).trans (gaugeAction g)
  gaugeAction_vacuum : ∀ g, gaugeAction g vacuum = vacuum
  /-- The spectrum of the Hamiltonian (the generator of time translations). -/
  energy : Set ℝ
  /-- Spectra of self-adjoint operators are closed. -/
  energy_closed : IsClosed energy
  /-- Positivity of the energy. -/
  energy_nonneg : ∀ E ∈ energy, 0 ≤ E
  /-- The vacuum has energy `0`. -/
  vacuum_energy : (0 : ℝ) ∈ energy

attribute [instance] QuantumTheory.normedAddCommGroup QuantumTheory.innerProductSpace
  QuantumTheory.completeSpace QuantumTheory.gaugeGroupGroup

/-- The Yang–Mills existence and mass gap conjecture, stated relative to a predicate
`IsYangMills` singling out those quantum theories whose Wightman functions are those of
quantum Yang–Mills theory on `ℝ⁴` with a given compact simple gauge group:
there exists such a theory, and its Hamiltonian has a positive mass gap. -/
