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
noncomputable def classNumberConstant : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

/-- Key intermediate lemma: the residue at `s = 1` of the Dedekind zeta function of `K`
is the explicit constant `(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`. -/
theorem dedekindZeta_residue_eq_classNumberConstant :
    dedekindZeta_residue K = classNumberConstant K :=
  dedekindZeta_residue_def K

/-- The constant is positive; in particular the residue is nonzero. -/
theorem classNumberConstant_pos : 0 < classNumberConstant K :=
  (dedekindZeta_residue_eq_classNumberConstant K) ▸ dedekindZeta_residue_pos K

/-- **The analytic class number formula.**
For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`
with residue
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`,
where `r₁` (resp. `r₂`) is the number of real (resp. complex) places of `K`, `R_K` is the
regulator, `h_K` the class number, `w_K` the number of roots of unity in `K`, and `d_K` the
discriminant. -/
theorem class_number_formula :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|) : ℝ) : ℂ)) := by
  have h := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  rwa [dedekindZeta_residue_eq_classNumberConstant K, classNumberConstant] at h

/-- Uniqueness form of the class number formula: any limit of `(s - 1) * ζ_K(s)` as `s → 1⁺`
must equal the explicit class number constant. -/
theorem eq_classNumberConstant_of_tendsto {L : ℂ}
    (hL : Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 L)) :
    L = (classNumberConstant K : ℂ) :=
  tendsto_nhds_unique hL (class_number_formula K)

end Math2

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

