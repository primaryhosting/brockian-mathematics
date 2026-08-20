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

lemma norm_weylAvg_le (x : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) (N : ℕ) :
    ‖weylAvg x (⇑f) N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weylAvg]
  · have h1 : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ (N : ℝ) * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ :=
            Finset.sum_le_sum fun n _ => f.norm_coe_le_norm (x n)
        _ = (N : ℝ) * ‖f‖ := by simp
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [weylAvg, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hNpos]
    exact h1.trans_eq (by ring)

/-- The integral against the Haar probability measure is bounded by the sup norm. -/
