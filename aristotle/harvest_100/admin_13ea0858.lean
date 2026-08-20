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
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

open Filter Topology

/-- `logicalErrorRate c p k` is the failure probability of a logical gate protected by `k`
levels of code concatenation, in the standard recursive model of fault tolerance:
a level-`0` (unencoded) gate fails with probability `p`, and a level-`(k+1)` gate fails only if
at least two of its level-`k` constituent blocks fail, which happens with probability at most
`c * (level-k failure rate)^2`, where `c` counts the malignant pairs of fault locations in the
fault-tolerant gadget. -/
noncomputable def logicalErrorRate (c p : ℝ) : ℕ → ℝ
  | 0 => p
  | k + 1 => c * (logicalErrorRate c p k) ^ 2

@[simp] theorem logicalErrorRate_zero (c p : ℝ) : logicalErrorRate c p 0 = p := rfl

@[simp] theorem logicalErrorRate_succ (c p : ℝ) (k : ℕ) :
    logicalErrorRate c p (k + 1) = c * (logicalErrorRate c p k) ^ 2 := rfl

/-- Exact solution of the concatenation recursion: after `k` levels of concatenation the
rescaled error rate is `(c * p)` raised to the power `2 ^ k`. -/
theorem c_mul_logicalErrorRate (c p : ℝ) (k : ℕ) :
    c * logicalErrorRate c p k = (c * p) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
      rw [logicalErrorRate_succ, h, pow_mul, ← ih]
      ring

/-- The error rate at level `k`, explicitly. -/
theorem logicalErrorRate_eq (c p : ℝ) (hc : c ≠ 0) (k : ℕ) :
    logicalErrorRate c p k = (c * p) ^ (2 ^ k) / c := by
  rw [← c_mul_logicalErrorRate c p k]
  field_simp

/-- **Threshold theorem** (error-suppression form).  Let `c > 0` be the constant counting
malignant fault pairs of the fault-tolerant gadgets, so that the concatenation recursion is
`p ↦ c * p ^ 2`, and let `p ≥ 0` be the physical error rate.  If `p` lies *below the threshold*
`p_th = 1 / c`, then the logical error rate of a computation protected by `k` levels of
concatenation can be made smaller than any prescribed accuracy `ε > 0` by taking `k` large
enough: fault-tolerant quantum computation to arbitrary accuracy is possible. -/
theorem threshold_theorem {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (hthr : p < 1 / c) :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, logicalErrorRate c p k < ε := by
  have hq0 : 0 ≤ c * p := mul_nonneg hc.le hp
  have hq1 : c * p < 1 := by
    have := (lt_div_iff₀' hc).1 hthr
    linarith
  -- `(c * p) ^ n → 0`
  have h1 : Tendsto (fun n : ℕ => (c * p) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℕ))
  have h3 : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k)) atTop (𝓝 0) := h1.comp h2
  have h4 : Tendsto (fun k : ℕ => logicalErrorRate c p k) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k) / c) atTop (𝓝 (0 / c)) :=
      h3.div_const c
    simpa [logicalErrorRate_eq c p hc.ne'] using this
  intro ε hε
  have := (h4.eventually (eventually_lt_nhds hε)).exists_forall_of_atTop
  obtain ⟨K, hK⟩ := this
  exact ⟨K, hK⟩

/-- Above the threshold the recursion makes things worse: the level-`k` error rate diverges. -/
theorem above_threshold {c p : ℝ} (hc : 0 < c) (hthr : 1 / c < p) :
    Tendsto (fun k : ℕ => logicalErrorRate c p k) atTop atTop := by
  have hq1 : 1 < c * p := by
    have := (div_lt_iff₀' hc).1 hthr
    linarith
  have h1 : Tendsto (fun n : ℕ => (c * p) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq1
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℕ))
  have h3 : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k)) atTop atTop := h1.comp h2
  have : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k) / c) atTop atTop :=
    h3.atTop_div_const hc
  simpa [logicalErrorRate_eq c p hc.ne'] using this

end QI

