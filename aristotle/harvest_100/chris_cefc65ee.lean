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

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

open scoped Real

namespace Math2

/--
**The analytic (Dirichlet) class number formula.**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`, with
residue

`(2 ^ r₁ * (2π) ^ r₂ * Reg K * h K) / (w K * √|disc K|)`,

where `r₁` is the number of real places, `r₂` the number of complex places, `Reg K` the regulator,
`h K` the class number, `w K` the number of roots of unity in `K`, and `disc K` the discriminant.

This is stated as the limit of `(s - 1) * ζ_K s` as `s → 1⁺` along the reals.
-/
theorem class_number_formula (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|) : ℝ) : ℂ)) :=
  tendsto_sub_one_mul_dedekindZeta_nhdsGT K

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

