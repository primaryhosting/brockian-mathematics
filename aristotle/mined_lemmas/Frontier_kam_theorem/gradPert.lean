/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Real Finset RealInnerProductSpace

namespace Frontier

/-- One factor of phase space, `ℝⁿ`.  It is used both for the action variables `p`
and for the angle variables `q`; the angles are understood modulo the lattice `2π ℤⁿ`. -/
abbrev Phase (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The Fourier mode `k ∈ ℤⁿ`, viewed as a vector of `ℝⁿ`. -/

noncomputable def gradPert (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (θ : Phase n) : Phase n :=
  ∑ k ∈ K, (-(a k) * sin ⟪mode k, θ⟫ + b k * cos ⟪mode k, θ⟫) • mode k

/-- The nearly integrable Hamiltonian `H_ε(p,q) = ⟪ω,p⟫ + ε f(q)`. -/
