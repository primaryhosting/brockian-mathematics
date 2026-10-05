import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

set_option grind.warning false

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

noncomputable def fockHamiltonian (hbar omega : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omega : ℝ) : ℂ) • (fockB ∘ₗ fockA + (1 / 2 : ℂ) • LinearMap.id)

/--
The Landau level theorem is not vacuous: in the explicit Bargmann–Fock model (where the
ladder operators are differentiation and multiplication by the variable, with the Bargmann
inner product) all hypotheses hold, and the states `(a†)ⁿ ψ₀` are nonzero eigenstates of
the Landau Hamiltonian with energies `ℏ ω_c (n + 1/2)`, `ω_c = q B / m`.
-/
