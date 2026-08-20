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

lemma fourier_coe_ne_one {a : ℝ} (ha : Irrational (a / T)) {k : ℤ} (hk : k ≠ 0) :
    fourier k ((a : ℝ) : AddCircle T) ≠ 1 := by
  rw [fourier_coe_apply]
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨m, hm⟩ := hcon
  have hTR : (T : ℝ) ≠ 0 := hT.out.ne'
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hTR
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hm
  have keyR : (k : ℝ) * a = T * (m : ℝ) := by exact_mod_cast hm
  refine ha ⟨(m : ℚ) / (k : ℚ), ?_⟩
  push_cast
  field_simp
  linarith [keyR]

/-- **Weyl's equidistribution theorem for irrational rotations.**  If `α / T` is irrational then
the orbit `n ↦ n α` is equidistributed in `ℝ / T ℤ`.  In particular the hypothesis of
`equidistribution_of_asymptotic` is satisfiable. -/
