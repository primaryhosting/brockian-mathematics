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
Unfolding of the Dedekind zeta function used in `Math2.class_number_formula`: it is the `L`-series
whose `n`-th coefficient counts the integral ideals of `𝓞 K` of absolute norm `n`, i.e.
`ζ_K(s) = ∑' n, #{I : Ideal (𝓞 K) // absNorm I = n} / n ^ s`.
-/

theorem dedekindZeta_eq_LSeries (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    dedekindZeta K s =
      LSeries (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s := rfl

/--
**The analytic class number formula.**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`, and the
residue there is given explicitly by

`lim_{s → 1⁺} (s - 1) ζ_K(s) = 2^{r₁} (2π)^{r₂} R_K h_K / (w_K √|d_K|)`,

where `r₁` is the number of real places, `r₂` the number of complex places, `R_K` the regulator,
`h_K` the class number, `w_K` the number of roots of unity in `K`, and `d_K` the discriminant.

The statement is phrased as a limit along `𝓝[>] 1` of the real-variable function
`s ↦ (s - 1) * ζ_K(s)` (with `ζ_K` the Dedekind zeta function of `K`, viewed on the reals via the
coercion `ℝ → ℂ`), and in particular records that this residue is a positive real number.
-/
