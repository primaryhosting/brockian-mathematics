/-
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

namespace Math2

/--
**The analytic class number formula.**

For a number field `K`, the Dedekind zeta function `ζ_K(s)`, defined as the `L`-series whose
`n`-th coefficient is the number of integral ideals of `𝓞 K` of absolute norm `n`, has a simple
pole at `s = 1` whose residue is

  `(2 ^ r₁ * (2π) ^ r₂ * Reg_K * h_K) / (w_K * √|d_K|)`,

where `r₁` (resp. `r₂`) is the number of real (resp. complex) places of `K`, `Reg_K` is the
regulator, `h_K` the class number, `w_K` the number of roots of unity in `K`, and `d_K` the
discriminant. This is stated as: `(s - 1) * ζ_K(s)` tends to that quantity as the real variable
`s` tends to `1` from above.
-/
theorem class_number_formula (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|) : ℝ) : ℂ)) := by
  rw [← dedekindZeta_residue_def]
  exact tendsto_sub_one_mul_dedekindZeta_nhdsGT K

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

