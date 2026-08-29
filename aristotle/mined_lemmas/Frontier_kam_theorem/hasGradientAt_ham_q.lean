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

lemma hasGradientAt_ham_q (p q : Phase n) :
    HasGradientAt (fun y => ham ω K a b ε p y) (ε • gradPert K a b q) q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (pert K a b)
      ((InnerProductSpace.toDual ℝ (Phase n)) (gradPert K a b q)) q :=
    (hasGradientAt_pert K a b q).hasFDerivAt
  have h2 := (h1.const_mul ε).const_add ⟪ω, p⟫
  have : HasFDerivAt (fun y => ham ω K a b ε p y)
      (ε • (InnerProductSpace.toDual ℝ (Phase n)) (gradPert K a b q)) q := by
    simpa [ham] using h2
  convert this using 1
  ext y
  simp

