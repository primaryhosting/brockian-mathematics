/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` to be the first command in a file, so this header is written as a
plain block comment `/- ... -/` rather than a module docstring `/-! ... -/`; the text is otherwise
exactly as specified.
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Phys

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

theorem bhEntropy_eq_bekensteinBound {k hbar c G M : ℝ} (hc : c ≠ 0) :
    bhEntropy k hbar c G M
      = bekensteinBound k hbar c (schwarzschildRadius G c M) (M * c ^ 2) := by
  unfold bhEntropy bekensteinBound schwarzschildRadius
  field_simp
  ring

/-- The mass increment delivered to a black hole of mass `M` when a body of energy `E` and
radius `R`, first lowered quasi-statically to proper distance `R` from the horizon, is dropped
in: the redshift factor there is `R / (2 R_s)` with `R_s = 2 G M / c ^ 2`, so the energy
delivered at infinity is `E R c ^ 2 / (4 G M)`, i.e. a mass `E R / (4 G M)`. -/
