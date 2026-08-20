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
/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QI

/-- The logical error rate of a level-`L` concatenated code, in the standard
recursive model of fault tolerance: one level of concatenation replaces a physical
error rate `x` by `C * x ^ 2` (a logical failure requires at least two independent
failures among the constituent blocks, with `C` counting the malignant pairs).
`C` is the inverse of the accuracy threshold `p_th = 1 / C`. -/

theorem threshold_theorem (C p : ℝ) (hC : 0 < C) (hp : 0 ≤ p) (hlt : p < 1 / C) :
    (∀ L : ℕ, logicalError C p L = (1 / C) * (p / (1 / C)) ^ (2 ^ L)) ∧
      Filter.Tendsto (logicalError C p) Filter.atTop (nhds 0) ∧
      ∀ ε > 0, ∃ L : ℕ, logicalError C p L < ε := by
  have hCp : C * p < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hC).mp hlt
  have hCp0 : 0 ≤ C * p := mul_nonneg hC.le hp
  have key : ∀ L : ℕ, logicalError C p L = (1 / C) * (C * p) ^ (2 ^ L) := by
    intro L
    have := logicalError_closed_form C p L
    field_simp at this ⊢
    linarith [this]
  have hform : ∀ L : ℕ, logicalError C p L = (1 / C) * (p / (1 / C)) ^ (2 ^ L) := by
    intro L
    rw [key L]
    congr 2
    field_simp
  have htend : Filter.Tendsto (logicalError C p) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (C * p) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hCp0 hCp
    have h2 : Filter.Tendsto (fun L : ℕ => 2 ^ L) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    have h3 : Filter.Tendsto (fun L : ℕ => (C * p) ^ (2 ^ L)) Filter.atTop (nhds 0) :=
      h1.comp h2
    have := h3.const_mul (1 / C)
    simp only [mul_zero] at this
    exact this.congr (fun L => (key L).symm)
  refine ⟨hform, htend, ?_⟩
  intro ε hε
  have := (htend.eventually (eventually_lt_nhds hε)).exists
  simpa using this

/-- Below threshold the modelled error rates are nonnegative. -/
