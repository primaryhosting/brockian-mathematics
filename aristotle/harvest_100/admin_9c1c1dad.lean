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
noncomputable def partitionFunction (β : ℝ) (E : α → ℝ) : ℝ :=
  ∑ i : α, Real.exp (-β * E i)

/-- The Helmholtz free energy `F = -(1/β) log Z`. -/
noncomputable def freeEnergy (β : ℝ) (E : α → ℝ) : ℝ :=
  -(Real.log (partitionFunction β E)) / β

/-- The Boltzmann (equilibrium) probability of the state `i`. -/
noncomputable def boltzmann (β : ℝ) (E : α → ℝ) (i : α) : ℝ :=
  Real.exp (-β * E i) / partitionFunction β E

/-- The partition function of a finite system is strictly positive. -/
lemma partitionFunction_pos [Nonempty α] (β : ℝ) (E : α → ℝ) :
    0 < partitionFunction β E := by
  refine Finset.sum_pos (fun i _ => Real.exp_pos _) ?_
  simpa using (Finset.univ_nonempty (α := α))

/-- The Boltzmann distribution is a probability distribution. -/
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
theorem jarzynski_equality [Nonempty α] (β : ℝ) (hβ : β ≠ 0) (EA EB : α → ℝ)
    (τ : Equiv.Perm α) (W : α → ℝ) (hW : ∀ i, W i = EB (τ i) - EA i) :
    ∑ i : α, boltzmann β EA i * Real.exp (-β * W i) =
      Real.exp (-β * (freeEnergy β EB - freeEnergy β EA)) := by
  have hZA : (0 : ℝ) < partitionFunction β EA := partitionFunction_pos β EA
  have hZB : (0 : ℝ) < partitionFunction β EB := partitionFunction_pos β EB
  -- The right-hand side is the ratio of partition functions.
  have hrhs : Real.exp (-β * (freeEnergy β EB - freeEnergy β EA)) =
      partitionFunction β EB / partitionFunction β EA := by
    unfold freeEnergy
    have : -β * (-(Real.log (partitionFunction β EB)) / β -
        -(Real.log (partitionFunction β EA)) / β) =
        Real.log (partitionFunction β EB) - Real.log (partitionFunction β EA) := by
      field_simp
      ring
    rw [this, Real.exp_sub, Real.exp_log hZB, Real.exp_log hZA]
  rw [hrhs]
  -- The left-hand side simplifies term by term.
  have hterm : ∀ i : α, boltzmann β EA i * Real.exp (-β * W i)
      = Real.exp (-β * EB (τ i)) / partitionFunction β EA := by
    intro i
    unfold boltzmann
    rw [hW i, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div]
  congr 1
  exact Equiv.sum_comp τ (fun j => Real.exp (-β * EB j))

end Jarzynski

end Phys

