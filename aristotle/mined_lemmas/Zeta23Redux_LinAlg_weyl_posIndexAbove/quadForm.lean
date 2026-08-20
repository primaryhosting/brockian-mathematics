import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, A x⟫` attached to a complex matrix `A`,
seen as an operator on `EuclideanSpace ℂ (Fin d)`. -/

noncomputable def quadForm (A : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  RCLike.re (inner ℂ x ((Matrix.toEuclideanLin A) x))

