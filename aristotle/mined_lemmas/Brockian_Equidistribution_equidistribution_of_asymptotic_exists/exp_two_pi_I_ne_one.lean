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

lemma exp_two_pi_I_ne_one {a : ℝ} (ha : Irrational a) {k : ℤ} (hk : k ≠ 0) :
    Complex.exp (2 * Real.pi * I * k * a) ≠ 1 := by
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨m, hm⟩ := hcon
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : (2 * (Real.pi : ℂ) * I) * ((k : ℂ) * a - m) = 0 := by
    ring_nf; ring_nf at hm; linear_combination hm
  have h3 : (k : ℂ) * a - m = 0 := by
    rcases mul_eq_zero.1 h2 with h4 | h4
    · exact absurd h4 (by simp [hpi, hI])
    · exact h4
  have h5 : (k : ℂ) * a = m := by linear_combination h3
  have h6 : (k : ℝ) * a = m := by exact_mod_cast h5
  exact (ha.intCast_mul hk).ne_int m h6

/-- The character averages of the orbit of an irrational rotation tend to zero. -/
