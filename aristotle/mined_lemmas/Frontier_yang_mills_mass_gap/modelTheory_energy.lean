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

@[simp] theorem modelTheory_energy (spec : Set ℝ) (hc : IsClosed spec) (hn : ∀ E ∈ spec, 0 ≤ E)
    (h0 : (0 : ℝ) ∈ spec) : (modelTheory spec hc hn h0).energy = spec := rfl

/-- The hypotheses of `Frontier.yang_mills_mass_gap` are satisfiable: for the (placeholder)
selection predicate `fun _ => True`, a free massive model theory of mass `1` together with
the constant sequence of regularisations satisfies them, and the reduction yields the
conclusion. -/
example : YangMillsMassGap (fun _ => True) := by
  have hn : ∀ E ∈ ({(0 : ℝ)} ∪ Set.Ici (1 : ℝ)), 0 ≤ E := by
    rintro E (rfl | hE)
    · exact le_refl 0
    · linarith [Set.mem_Ici.mp hE]
  set T := modelTheory ({(0 : ℝ)} ∪ Set.Ici (1 : ℝ)) (isClosed_gapSet 1) hn (Or.inl rfl) with hT
  refine yang_mills_mass_gap _ T (fun _ => T) 1 trivial ?_ ?_
  · intro E hE
    exact ⟨fun _ => E, fun _ => hE, tendsto_const_nhds⟩
  · intro _
    rw [hT, modelTheory_energy]
    exact free_massive_hasMassGap one_pos

end Frontier

import Mathlib

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

