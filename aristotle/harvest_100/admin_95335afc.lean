import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real Topology
open Filter NumberField NumberField.InfinitePlace NumberField.Units

namespace Math2

/--
**The analytic class number formula.**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`, with
residue
```
      2 ^ r₁ * (2π) ^ r₂ * R_K * h_K
    ----------------------------------
        w_K * sqrt |disc K|
```
where `r₁` is the number of real places, `r₂` the number of complex places, `R_K` the regulator,
`h_K` the class number, `w_K` the number of roots of unity in `K`, and `disc K` the discriminant.

Formally: `(s - 1) * ζ_K s` tends to this quantity as `s → 1⁺`, and the quantity is a strictly
positive real number.
-/
theorem class_number_formula (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ)) ∧
      0 < ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) := by
  constructor
  · simpa only [dedekindZeta_residue_def] using tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  · simpa only [dedekindZeta_residue_def] using dedekindZeta_residue_pos K

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

