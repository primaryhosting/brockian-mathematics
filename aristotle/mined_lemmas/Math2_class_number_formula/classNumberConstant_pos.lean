import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

open scoped Real

namespace Math2

variable (K : Type*) [Field K] [NumberField K]

/-- The explicit constant appearing in the analytic class number formula:
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`. -/

theorem classNumberConstant_pos : 0 < classNumberConstant K :=
  (dedekindZeta_residue_eq_classNumberConstant K) ▸ dedekindZeta_residue_pos K

/-- **The analytic class number formula.**
For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`
with residue
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`,
where `r₁` (resp. `r₂`) is the number of real (resp. complex) places of `K`, `R_K` is the
regulator, `h_K` the class number, `w_K` the number of roots of unity in `K`, and `d_K` the
discriminant. -/
