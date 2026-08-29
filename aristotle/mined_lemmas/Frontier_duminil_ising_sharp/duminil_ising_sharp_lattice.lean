/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

namespace Frontier

/-!
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/

theorem duminil_ising_sharp_lattice (d : ℕ) (i₀ : Fin d) (betaC : ℝ) (hbc : 0 < betaC)
    (hcorr0 : ∀ (β : ℝ) (n : ℕ), 0 ≤ isingCorr d i₀ β n)
    (hcorr1 : ∀ (β : ℝ) (n : ℕ), isingCorr d i₀ β n ≤ 1)
    (hsub : ∀ β, 0 ≤ β → β < betaC → ∃ L : ℕ, 0 < L ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ n : ℕ, isingCorr d i₀ β (n + L) ≤ c * isingCorr d i₀ β n)
    (hcont : ContinuousOn (isingSpontaneousMag d) (Set.Ici betaC))
    (hdiff : ∀ β ∈ Set.Ioi betaC, DifferentiableAt ℝ (isingSpontaneousMag d) β)
    (hineq : ∀ β ∈ Set.Ioi betaC,
      (1 - isingSpontaneousMag d β) / β ≤ deriv (isingSpontaneousMag d) β)
    (hmag0 : 0 ≤ isingSpontaneousMag d betaC) :
    (∀ β, 0 ≤ β → β < betaC → ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
        ∀ n : ℕ, isingCorr d i₀ β n ≤ C * Real.exp (-α * n)) ∧
      (∀ β, betaC < β → (β - betaC) / β ≤ isingSpontaneousMag d β ∧
        0 < isingSpontaneousMag d β) :=
  duminil_ising_sharp (isingCorr d i₀) (isingSpontaneousMag d) betaC hbc hcorr0 hcorr1 hsub
    hcont hdiff hineq hmag0

end Frontier

