import Mathlib
/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command in a file, so the header
-- module docstring above is placed immediately after the import.)

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

namespace Frontier

/-- The Mexican-hat scalar potential of the abelian Higgs toy model,
`V(φ) = lam * (|φ|² - v²)²`, written as a function of the modulus `r = |φ|`. -/

theorem higgsPotential_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (v r : ℝ) :
    0 ≤ higgsPotential lam v r :=
  mul_nonneg hlam (sq_nonneg _)

/-- The potential vanishes on the vacuum manifold `|φ| = v`. -/
