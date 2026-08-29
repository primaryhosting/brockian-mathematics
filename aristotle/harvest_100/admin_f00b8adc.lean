/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

variable {Ω : Type*} [Fintype Ω]

/-- Canonical partition function at inverse temperature `β` for a Hamiltonian `H`
on a finite phase space. -/
noncomputable def partitionFunction (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∑ x, Real.exp (-β * H x)

/-- Helmholtz free energy `F = -(1/β) log Z`. -/
noncomputable def freeEnergy (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction β H)

/-- The Gibbs (canonical) probability of the state `x`. -/
noncomputable def gibbs (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunction β H

/-- The work performed along the trajectory starting at `x`, when the system is driven
from the Hamiltonian `H₀` to `H₁` by the (measure-preserving, i.e. bijective)
deterministic evolution `φ`. -/
def work (H₀ H₁ : Ω → ℝ) (φ : Ω ≃ Ω) (x : Ω) : ℝ := H₁ (φ x) - H₀ x

theorem partitionFunction_pos [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) :
    0 < partitionFunction β H := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- **Jarzynski equality.**  For a system initially in thermal equilibrium with respect to
`H₀` at inverse temperature `β`, driven to the Hamiltonian `H₁` by a deterministic
volume-preserving (bijective) evolution `φ`, the exponential average of the work equals
`exp (-β ΔF)`, where `ΔF = F₁ - F₀` is the equilibrium free-energy difference. -/
theorem jarzynski_equality [Nonempty Ω] (β : ℝ) (hβ : β ≠ 0)
    (H₀ H₁ : Ω → ℝ) (φ : Ω ≃ Ω) :
    ∑ x, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ φ x)
      = Real.exp (-β * (freeEnergy β H₁ - freeEnergy β H₀)) := by
  have h0 : 0 < partitionFunction β H₀ := partitionFunction_pos β H₀
  have h1 : 0 < partitionFunction β H₁ := partitionFunction_pos β H₁
  have hLHS : ∑ x, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ φ x)
      = partitionFunction β H₁ / partitionFunction β H₀ := by
    rw [partitionFunction, Finset.sum_div]
    rw [← Equiv.sum_comp φ (fun y => Real.exp (-β * H₁ y) / partitionFunction β H₀)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [gibbs, work, div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  have hRHS : -β * (freeEnergy β H₁ - freeEnergy β H₀)
      = Real.log (partitionFunction β H₁) - Real.log (partitionFunction β H₀) := by
    simp only [freeEnergy]
    field_simp
    ring
  rw [hLHS, hRHS, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

end Phys

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

