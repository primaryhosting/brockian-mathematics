import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

/--
**The analytic class number formula (Dirichlet class number formula).**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1` whose
residue is
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`,
where `r₁` (resp. `r₂`) is the number of real (resp. complex) places of `K`, `R_K` is the
regulator, `h_K` the class number, `w_K` the number of roots of unity in `K` and `d_K` the
discriminant.  This is expressed as the limit of `(s - 1) * ζ_K(s)` as `s → 1⁺` along the reals.
-/

theorem card_infinitePlace_rat : Fintype.card (InfinitePlace ℚ) = 1 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, ← IsTotallyReal.finrank]
  simp

/-- `ℚ` has exactly one real place. -/
