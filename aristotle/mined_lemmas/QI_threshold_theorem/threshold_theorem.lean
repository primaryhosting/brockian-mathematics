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

/-- The logical error rate of a fault-tolerant scheme built by `k`-fold concatenation of a
distance-3 (single-error-correcting) code, starting from physical error rate `p`.

One level of concatenation replaces each gate by a fault-tolerant gadget which fails only if at
least two of its constituent locations fail; with `C` the number of malignant pairs of locations
in a gadget, the standard level-reduction estimate gives
`p_{k+1} = C * p_k ^ 2`. -/

theorem threshold_theorem (C : ℝ) (hC : 0 < C) :
    ∃ pth : ℝ, 0 < pth ∧ ∀ p : ℝ, 0 ≤ p → p < pth →
      (∀ k : ℕ, 0 ≤ logicalErrorRate C p k) ∧
      (∀ k : ℕ, logicalErrorRate C p (k + 1) ≤ logicalErrorRate C p k) ∧
      Filter.Tendsto (logicalErrorRate C p) Filter.atTop (nhds 0) ∧
      (∀ ε : ℝ, 0 < ε → ε < pth → ∃ k : ℕ, logicalErrorRate C p k < ε ∧
        (2 : ℝ) ^ k ≤ 2 * (Real.log (1 / (C * ε)) / Real.log (1 / (C * p)) + 1)) := by
  refine ⟨1 / C, by positivity, ?_⟩
  intro p hp hpth
  have hlt : C * p < 1 := by
    rw [lt_div_iff₀ hC] at hpth
    linarith
  refine ⟨logicalErrorRate_nonneg C p hC hp,
    logicalErrorRate_antitone C p hC hp hlt,
    tendsto_logicalErrorRate C p hC hp hlt, ?_⟩
  intro ε hε hεth
  have hεC : C * ε < 1 := by
    rw [lt_div_iff₀ hC] at hεth
    linarith
  exact exists_level C p hC hp hlt ε hε hεC

end QI

