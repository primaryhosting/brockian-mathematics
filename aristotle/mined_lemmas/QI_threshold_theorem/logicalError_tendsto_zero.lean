import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
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

namespace QI

/-- The logical error rate of a circuit location after `L` levels of code
concatenation, given a physical error rate `p` and a constant `c` counting the
number of malignant pairs of fault locations in one level-1 gadget.

One level of concatenation replaces each location by a gadget that fails only if
at least two of its locations fail, giving the standard recursion
`p_{L+1} = c * p_L ^ 2`. -/

theorem logicalError_tendsto_zero {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p)
    (hthr : c * p < 1) :
    Filter.Tendsto (fun L : ℕ => logicalError c p L) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := threshold_theorem hc hp hthr hε
  refine ⟨L₀, fun L hL => ?_⟩
  have hnonneg : 0 ≤ logicalError c p L := by
    rw [logicalError_eq_pow c p hc.ne']
    exact div_nonneg (pow_nonneg (mul_nonneg hc.le hp) _) hc.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hL₀ L hL

end QI

#print axioms QI.threshold_theorem
#print axioms QI.logicalError_tendsto_zero

