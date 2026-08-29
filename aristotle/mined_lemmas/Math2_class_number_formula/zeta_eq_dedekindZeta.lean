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

/-- The Dedekind zeta function of a number field `K`, written explicitly as the `L`-series
whose `n`-th coefficient is the number of integral ideals of `𝓞 K` of absolute norm `n`. -/

theorem zeta_eq_dedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    zeta K s = NumberField.dedekindZeta K s := rfl

/--
**The analytic class number formula.**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`, and its
residue there is
`2 ^ r₁ * (2 π) ^ r₂ * R_K * h_K / (w_K * √|d_K|)`,
where `r₁` is the number of real places, `r₂` the number of complex places, `R_K` the regulator,
`h_K` the class number, `w_K` the number of roots of unity in `K`, and `d_K` the discriminant.

Formally: `(s - 1) * ζ_K(s)` tends to this quantity as `s → 1` from the right along the reals.
-/
