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

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H`
on a finite phase space at inverse temperature `β`. -/

theorem average_work_ge_freeEnergy_diff [Nonempty Ω] (β : ℝ) (hβ : 0 < β)
    (H₀ H₁ : Ω → ℝ) (φ : Equiv.Perm Ω) :
    freeEnergy β H₁ - freeEnergy β H₀
      ≤ ∑ x, gibbs β H₀ x * work H₀ H₁ φ x := by
  have hjensen : Real.exp (∑ x, gibbs β H₀ x * (-β * work H₀ H₁ φ x))
      ≤ ∑ x, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ φ x) := by
    simpa [smul_eq_mul] using
      convexOn_exp.map_sum_le (t := (Finset.univ : Finset Ω)) (w := gibbs β H₀)
        (p := fun x => -β * work H₀ H₁ φ x)
        (fun i _ => gibbs_nonneg β H₀ i) (sum_gibbs β H₀) (fun i _ => Set.mem_univ _)
  rw [jarzynski_equality β hβ.ne' H₀ H₁ φ] at hjensen
  have hsum : ∑ x, gibbs β H₀ x * (-β * work H₀ H₁ φ x)
      = -β * ∑ x, gibbs β H₀ x * work H₀ H₁ φ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsum] at hjensen
  have := Real.exp_le_exp.mp hjensen
  nlinarith [this]

section Continuous

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Partition function on a general (continuous) phase space with reference measure `μ`
(e.g. Liouville measure): `Z = ∫ e^{-βH} dμ`. -/
