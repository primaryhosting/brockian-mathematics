/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment because Lean 4 does not allow a
-- module docstring `/-! ... -/` to appear before the `import` commands.)

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math

open Polynomial

/-- The sixth cyclotomic polynomial over `ℂ` has `nextCoeff = -1`. -/

lemma nextCoeff_cyclotomic_six : (cyclotomic 6 ℂ).nextCoeff = -1 := by
  rw [Polynomial.cyclotomic_six]
  have hdeg : (X ^ 2 - X + 1 : ℂ[X]).natDegree = 2 := by
    compute_degree!
  rw [Polynomial.nextCoeff, hdeg]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

/-- **Sum of the primitive 6-th roots of unity.**
The sum of the primitive `6`-th roots of unity in `ℂ` equals the Möbius function `μ(6) = 1`. -/
