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

lemma gradient_ham_q (p q : Phase n) :
    gradient (fun y => ham ω K a b ε p y) q = ε • gradPert K a b q :=
  (hasGradientAt_ham_q ω K a b ε p q).gradient

/-- **Base case (`ε = 0`, the integrable system).**  For `H_0(p,q) = ⟪ω,p⟫` every torus
`{p = p₀}` is invariant and carries the linear flow `θ ↦ θ + t ω`. -/
