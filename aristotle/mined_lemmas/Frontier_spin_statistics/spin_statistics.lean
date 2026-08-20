/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem spin_statistics {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {TF : Type*} (Φ : WightmanField H TF) (hnontrivial : ∃ f, Φ.field f ≠ 0) :
    Φ.stat = statisticsOfSpin Φ.twiceSpin := by
  by_contra hwrong
  obtain ⟨f, hf⟩ := hnontrivial
  exact hf (Φ.trivial_of_wrong_statistics hwrong f)

/-! ## Non-vacuity

We exhibit a model of the axioms carrying a nonzero field, so that the hypotheses of
`Frontier.spin_statistics` are consistent and the theorem is not vacuous.  The model has
one-dimensional state space `ℂ`, test functions indexed by spacetime points, and the
identity operator as field; it is a spin-`0`, Bose model.
-/

/-- Two distinct points of a spacelike hyperplane are spacelike separated. -/
