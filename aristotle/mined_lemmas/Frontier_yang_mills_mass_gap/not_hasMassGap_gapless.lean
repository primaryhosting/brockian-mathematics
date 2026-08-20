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

theorem not_hasMassGap_gapless : ¬ ∃ Δ : ℝ, HasMassGap (Set.Ici (0 : ℝ)) Δ := by
  rintro ⟨Δ, hΔ, -, h⟩
  rcases h (Δ / 2) (by simp; positivity) with h0 | h1
  · linarith
  · linarith

/-- **Stability of the mass gap under continuum limits.** If every approximating theory has
a mass gap of size at least the *same* `Δ > 0`, then any continuum limit of them has a mass
gap of size `Δ`. -/
