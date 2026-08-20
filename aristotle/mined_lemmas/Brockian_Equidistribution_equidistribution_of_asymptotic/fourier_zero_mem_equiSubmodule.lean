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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology Submodule Set
open AddCircle (haarAddCircle)

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th Weyl average of `f` along the sequence `x`, i.e.
`(1/N) * ∑_{n < N} f (x n)` (equal to `0` when `N = 0`). -/

lemma fourier_zero_mem_equiSubmodule (x : ℕ → AddCircle T) :
    (fourier (0 : ℤ) : C(AddCircle T, ℂ)) ∈ equiSubmodule x := by
  rw [mem_equiSubmodule_iff, integral_fourier_zero]
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℕ)))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have hsum : ∑ _n ∈ Finset.range N, (fourier (0 : ℤ) : C(AddCircle T, ℂ)) (x _n) = (N : ℂ) := by
    simp
  rw [weylAvg, hsum, inv_mul_cancel₀ hN0]

/-!
### Main theorem

Weyl's criterion.  The hypothesis of the conditional version — that the linear span of the
characters is dense in `C(AddCircle T, ℂ)` — is discharged unconditionally using Mathlib's
`span_fourier_closure_eq_top` (a consequence of the Stone–Weierstrass theorem), so the statement
below carries no auxiliary assumption beyond the vanishing of the Weyl sums.
-/

/-- **Weyl's equidistribution criterion.**  If for every nonzero integer `k` the Weyl sums
`(1/N) ∑_{n < N} e(k xₙ)` tend to `0`, then the sequence `x` is equidistributed in the circle
`ℝ / T ℤ`: the averages of every continuous function converge to its mean value.

This is unconditional: the density input is supplied by `span_fourier_closure_eq_top`. -/
