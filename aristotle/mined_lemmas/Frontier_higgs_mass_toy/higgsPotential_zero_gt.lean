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

theorem higgsPotential_zero_gt {lam v : ℝ} (hlam : 0 < lam) (hv : v ≠ 0) :
    higgsPotential lam v v < higgsPotential lam v 0 := by
  have : 0 < lam * (v ^ 2) ^ 2 := by positivity
  simpa [higgsPotential] using this

/-- The gauge-kinetic term evaluated on the vacuum configuration produces exactly a
mass term `m² A²` for the gauge field, with `m² = g² v²`. -/
