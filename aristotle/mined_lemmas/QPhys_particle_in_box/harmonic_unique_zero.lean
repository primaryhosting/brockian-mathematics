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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well
of width `L`: `E n = n² π² ℏ² / (2 m L²)`. -/

theorem harmonic_unique_zero (c : ℝ) (hc : 0 < c) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (h0 : f 0 = 0) (h0' : f' 0 = 0) : ∀ x : ℝ, f x = 0 := by
  intro x
  have h := harmonic_invariant c f f' hf hf' x 0
  rw [h0, h0'] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  have hb : (f x) ^ 2 = 0 := by nlinarith [sq_nonneg (f' x), sq_nonneg (f x)]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb

/-- For `c ≤ 0` there is no nontrivial solution of `f'' = -c f` vanishing at `0` and `L`. -/
