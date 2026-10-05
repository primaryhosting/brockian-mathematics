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

lemma hasGradientAt_ham_p (q p : Phase n) :
    HasGradientAt (fun x => ham ω K a b ε x q) ω p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (fun x : Phase n => ⟪ω, x⟫)
      ((InnerProductSpace.toDual ℝ (Phase n)) ω) p :=
    (hasGradientAt_inner_left ω p).hasFDerivAt
  simpa [ham] using h.add_const (ε * pert K a b q)

