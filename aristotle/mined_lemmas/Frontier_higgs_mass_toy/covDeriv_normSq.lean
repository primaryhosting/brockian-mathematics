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

theorem covDeriv_normSq {g v A : ℝ} {phi : ℂ} (hphi : ‖phi‖ = v) :
    ‖covDeriv g A phi‖ ^ 2 = gaugeMassSq g v * A ^ 2 := by
  have h : ‖covDeriv g A phi‖ = |g * A| * v := by
    simp [covDeriv, hphi]
  rw [h, gaugeMassSq]
  rw [mul_pow, sq_abs]
  ring

/-- **Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

For a quartic coupling `lam > 0`, a nonzero vacuum expectation value `v > 0` and a nonzero
gauge coupling `g`:

* the Mexican-hat potential `V(r) = lam (r² - v²)²` is nonnegative and attains its minimum
  value `0` on the vacuum manifold `r = v`, while the symmetric point `r = 0` has strictly
  higher energy (so the `U(1)` symmetry is spontaneously broken);
* evaluating the gauge-covariant kinetic term on the vacuum configuration `‖φ‖ = v` yields
  precisely the mass term `m² A²`;
* the resulting gauge boson mass squared `m² = g² v²` is strictly positive.
-/
