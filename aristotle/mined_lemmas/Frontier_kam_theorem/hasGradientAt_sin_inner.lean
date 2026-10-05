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

lemma hasGradientAt_sin_inner (v x : Phase n) :
    HasGradientAt (fun y => sin ⟪v, y⟫) ((cos ⟪v, x⟫) • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y => ⟪v, y⟫) (innerSL ℝ v) x := by
    simpa using (innerSL ℝ v).hasFDerivAt
  have h2 := (Real.hasDerivAt_sin ⟪v, x⟫).comp_hasFDerivAt x h1
  convert h2 using 1
  ext y; simp

/-- `gradPert` really is the gradient of the perturbation. -/
