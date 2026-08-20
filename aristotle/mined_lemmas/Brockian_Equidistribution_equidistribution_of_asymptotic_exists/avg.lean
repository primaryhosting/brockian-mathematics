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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution: existence of the asymptotic average

This file develops Weyl's criterion for equidistribution modulo one on the circle
`AddCircle (1 : ℝ) = ℝ / ℤ`, and deduces from it Weyl's equidistribution theorem for the
sequence `n ↦ n * a` with `a` irrational.

Main results:

* `Brockian.Equidistribution.isEquidistributed_of_tendsto_fourier`: Weyl's criterion.
* `Brockian.Equidistribution.isEquidistributed_irrational`: the orbit of an irrational
  rotation is equidistributed mod 1.
* `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`: unconditional statement
  that for irrational `a` the asymptotic average of any continuous function along `n * a`
  exists and equals the integral of the function.
-/

open MeasureTheory Filter Complex
open scoped Topology BigOperators

namespace Brockian.Equidistribution

local instance factZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The Birkhoff-type average of a continuous function `f` on the circle `ℝ / ℤ` along the
first `N` points of the real sequence `x`, taken modulo `1`. -/

noncomputable def avg (x : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : AddCircle (1 : ℝ))

/-- A real sequence is *equidistributed mod 1* if the averages of every continuous function on
the circle along the sequence converge to the integral of that function with respect to the
Haar probability measure. -/
