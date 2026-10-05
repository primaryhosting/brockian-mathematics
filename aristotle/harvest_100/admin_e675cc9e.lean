import Mathlib
/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H` on a finite
state space at inverse temperature `β`. -/
noncomputable def partitionFunction (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∑ x : Ω, Real.exp (-β * H x)

/-- Helmholtz free energy `F = -(1/β) log Z`. -/
noncomputable def freeEnergy (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction β H)

/-- The Gibbs (canonical equilibrium) distribution `p(x) = e^{-βH(x)}/Z`. -/
noncomputable def gibbs (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunction β H

/-- The work performed along the deterministic trajectory started at `x`: the protocol
switches the Hamiltonian from `H₀` to `H₁` while the (Liouville, i.e. phase-space
volume preserving) dynamics carries `x` to `Φ x`. -/
def work (H₀ H₁ : Ω → ℝ) (Φ : Equiv.Perm Ω) (x : Ω) : ℝ := H₁ (Φ x) - H₀ x

lemma partitionFunction_pos [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) :
    0 < partitionFunction β H := by
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Jarzynski equality.** For a system prepared in the Gibbs state of `H₀` and driven by an
arbitrary volume-preserving (Liouville) evolution `Φ` while the Hamiltonian is switched to `H₁`,
the exponential average of the work equals `e^{-βΔF}`, where `ΔF = F₁ - F₀` is the free-energy
difference between the equilibrium states of the two Hamiltonians. -/
theorem jarzynski_equality [Nonempty Ω] (β : ℝ) (hβ : β ≠ 0)
    (H₀ H₁ : Ω → ℝ) (Φ : Equiv.Perm Ω) :
    ∑ x : Ω, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ Φ x)
      = Real.exp (-β * (freeEnergy β H₁ - freeEnergy β H₀)) := by
  have h0 : 0 < partitionFunction β H₀ := partitionFunction_pos β H₀
  have h1 : 0 < partitionFunction β H₁ := partitionFunction_pos β H₁
  have hlhs : ∑ x : Ω, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ Φ x)
      = partitionFunction β H₁ / partitionFunction β H₀ := by
    have hterm : ∀ x : Ω, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ Φ x)
        = Real.exp (-β * H₁ (Φ x)) / partitionFunction β H₀ := by
      intro x
      rw [gibbs, work, div_mul_eq_mul_div, ← Real.exp_add]
      ring_nf
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_div,
      Equiv.sum_comp Φ (fun y => Real.exp (-β * H₁ y))]
    rfl
  rw [hlhs, freeEnergy, freeEnergy]
  have : -β * (-(1 / β) * Real.log (partitionFunction β H₁)
      - -(1 / β) * Real.log (partitionFunction β H₀))
      = Real.log (partitionFunction β H₁) - Real.log (partitionFunction β H₀) := by
    field_simp
    ring
  rw [this, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

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

