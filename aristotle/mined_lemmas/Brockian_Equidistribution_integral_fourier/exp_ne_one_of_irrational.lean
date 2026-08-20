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

import Mathlib

/-!
# Weyl's equidistribution criterion on the additive circle

This file develops equidistribution of sequences on `AddCircle T`.

* `Brockian.Equidistribution.Equidistributed x` says that the empirical averages of a sequence
  `x : ℕ → AddCircle T` converge, against every continuous test function, to the integral of the
  test function with respect to the normalised Haar (probability) measure.
* `Brockian.Equidistribution.WeylSumsVanish x` is the Weyl-sum hypothesis: the empirical averages
  of every nontrivial Fourier monomial `fourier k` (`k ≠ 0`) tend to `0`.
* `Brockian.Equidistribution.equidistribution_of_asymptotic` is the conditional statement
  (Weyl's criterion): `WeylSumsVanish x → Equidistributed x`.
* `Brockian.Equidistribution.weylSumsVanish_rotSeq` discharges the hypothesis for the
  irrational rotation sequence `n ↦ n * a` on `AddCircle 1`, and
  `Brockian.Equidistribution.equidistributed_irrational_rotation` is the resulting unconditional
  equidistribution theorem.
-/

open Filter Topology MeasureTheory AddCircle Complex Submodule Set

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The empirical average of `f` over the first `N` terms of the sequence `x`. -/

lemma exp_ne_one_of_irrational {a : ℝ} (ha : Irrational a) {k : ℤ} (hk : k ≠ 0) :
    Complex.exp (((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hka : ((k : ℝ) * a : ℝ) = (m : ℝ) := by
    have : (((k : ℝ) * a : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
      push_cast at hm ⊢
      field_simp at hm
      exact hm
    exact_mod_cast this
  exact (ha.intCast_mul hk).ne_int m hka

/-- Discharging the hypothesis of Weyl's criterion for an irrational rotation. -/
