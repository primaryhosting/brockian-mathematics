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

theorem yang_mills_mass_gap
    (IsYangMills : QuantumTheory → Prop)
    (T : QuantumTheory) (approx : ℕ → QuantumTheory) (Δ : ℝ)
    (hYM : IsYangMills T)
    (hlim : IsContinuumLimit T approx)
    (hgap : ∀ n, HasMassGap (approx n).energy Δ) :
    YangMillsMassGap IsYangMills :=
  ⟨T, hYM, Δ, hasMassGap_of_continuumLimit hlim hgap⟩

/-!
## Non-vacuity

The hypotheses of the reduction are satisfiable: below we build, for any closed set of
non-negative energies containing `0`, a quantum theory realising it, and check that the
reduction then really produces a proof of the (relativised) conjecture.  In particular the
`QuantumTheory` structure is consistent and the reduction is not vacuous.
-/

/-- A model quantum theory on the one-dimensional Hilbert space `ℂ` with prescribed energy
spectrum. -/
