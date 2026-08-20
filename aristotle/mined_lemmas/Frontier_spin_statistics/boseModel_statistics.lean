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

theorem boseModel_statistics :
    boseModel.stat = statisticsOfSpin boseModel.twiceSpin :=
  spin_statistics boseModel boseModel_nontrivial

/-! ### A nontrivial fermionic model

We also exhibit a *fermionic* model (`twiceSpin = 1`, Fermi statistics) with a nonzero
field, so that the axioms are consistent for half-integer spin as well.  The state space is
`ℂ²`, the field at a point `x` is the operator with matrix `!![0, d x; c x, 0]`, and the
coefficient functions `c`, `d` are supported on two timelike lines, chosen so that the
coefficient vectors at spacelike separated points are orthogonal.
-/

namespace FermiModel

open Matrix

/-- The two-dimensional state space of the model. -/
abbrev Hf := EuclideanSpace ℂ (Fin 2)

/-- The operator on `ℂ²` attached to a `2 × 2` matrix. -/
