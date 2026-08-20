import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- The homogeneous space `X = G / Γ` for `G = ℝ²` and the lattice `Γ = ℤ²`, i.e. the
two-dimensional torus. -/
abbrev Torus2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `G = ℝ² → X = ℝ²/ℤ²`. -/

def orbit (v : ℝ × ℝ) (x : Torus2) : Set Torus2 := {y | ∃ t : ℝ, y = x + flowHom v t}

/-- The closure of the orbit of the identity coset: a closed connected subgroup of `X`. -/
