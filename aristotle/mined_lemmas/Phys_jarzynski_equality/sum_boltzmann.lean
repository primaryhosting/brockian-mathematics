/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

section Jarzynski

variable {α : Type*} [Fintype α]

/-- The canonical (Boltzmann) partition function at inverse temperature `β` for the
energy function `E` on a finite state space. -/

lemma sum_boltzmann [Nonempty α] (β : ℝ) (E : α → ℝ) :
    ∑ i : α, boltzmann β E i = 1 := by
  unfold boltzmann
  rw [← Finset.sum_div]
  exact div_self (partitionFunction_pos β E).ne'

/--
**Jarzynski equality.**

Consider a finite classical system whose microstates form a finite nonempty set `α`.
The system starts in thermal equilibrium at inverse temperature `β ≠ 0` with respect to the
initial Hamiltonian `EA`, i.e. the state `i` occurs with the Boltzmann probability
`boltzmann β EA i = e^{-β EA i} / Z_A`.

A work protocol drives the system to a final Hamiltonian `EB`.  The microscopic dynamics is
deterministic, time-reversible and (by Liouville's theorem) measure preserving, so it is
described by a permutation `τ` of the state space: the state `i` is mapped to `τ i`.  The
work performed along this trajectory is `W i = EB (τ i) - EA i`.

Then the exponential average of the work equals the exponential of the free-energy difference:

  `⟨e^{-βW}⟩ = e^{-β ΔF}`,  with `ΔF = F_B - F_A`.
-/
