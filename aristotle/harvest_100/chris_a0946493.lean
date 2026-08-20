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
noncomputable def logicalError (C p : ℝ) : ℕ → ℝ
  | 0 => p
  | L + 1 => C * logicalError C p L ^ 2

@[simp] theorem logicalError_zero (C p : ℝ) : logicalError C p 0 = p := rfl

@[simp] theorem logicalError_succ (C p : ℝ) (L : ℕ) :
    logicalError C p (L + 1) = C * logicalError C p L ^ 2 := rfl

/-- Exact closed form: `C * p_L = (C * p) ^ (2 ^ L)`. -/
theorem logicalError_closed_form (C p : ℝ) (L : ℕ) :
    C * logicalError C p L = (C * p) ^ (2 ^ L) := by
  induction L with
  | zero => simp
  | succ L ih =>
      have : C * logicalError C p (L + 1) = (C * logicalError C p L) ^ 2 := by
        simp [logicalError]; ring
      rw [this, ih, ← pow_mul, pow_succ]

/--
**Threshold theorem** (concatenated-code form).

Let `p_th = 1 / C > 0` be the accuracy threshold of a fault-tolerant scheme whose
level-by-level error suppression obeys `p_{L+1} = C * p_L ^ 2`. If the physical
error rate `p` is nonnegative and strictly *below* the threshold, then:

* the level-`L` logical error rate is given exactly by
  `p_L = p_th * (p / p_th) ^ (2 ^ L)`, i.e. it decreases *doubly exponentially* in
  the number `L` of concatenation levels;
* consequently `p_L → 0`, so for every target accuracy `ε > 0` there is a level `L`
  achieving logical error below `ε`: arbitrarily accurate quantum computation is
  possible below the threshold.
-/
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
theorem logicalError_nonneg {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (L : ℕ) :
    0 ≤ logicalError C p L := by
  induction L with
  | zero => simpa using hp
  | succ L _ => exact mul_nonneg hC (sq_nonneg _)

/--
**Threshold theorem, robust form.**

The conclusion does not depend on the error rates following the recursion exactly:
any nonnegative sequence `q` of level-`L` logical error rates that starts below the
threshold (`q 0 ≤ p < 1 / C`) and is suppressed at least quadratically at each level
(`q (L+1) ≤ C * q L ^ 2`) is bounded by the doubly exponentially decaying sequence
`p_th * (p / p_th) ^ (2 ^ L)` and therefore converges to `0`.
-/
theorem threshold_theorem_of_le (C p : ℝ) (q : ℕ → ℝ) (hC : 0 < C) (hp : 0 ≤ p)
    (hlt : p < 1 / C) (hq0 : q 0 ≤ p) (hqnonneg : ∀ L, 0 ≤ q L)
    (hrec : ∀ L, q (L + 1) ≤ C * q L ^ 2) :
    (∀ L : ℕ, q L ≤ (1 / C) * (p / (1 / C)) ^ (2 ^ L)) ∧
      Filter.Tendsto q Filter.atTop (nhds 0) := by
  obtain ⟨hform, htend, -⟩ := threshold_theorem C p hC hp hlt
  have hle : ∀ L : ℕ, q L ≤ logicalError C p L := by
    intro L
    induction L with
    | zero => simpa using hq0
    | succ L ih =>
        refine (hrec L).trans ?_
        have hsq : q L ^ 2 ≤ logicalError C p L ^ 2 :=
          pow_le_pow_left₀ (hqnonneg L) ih 2
        simpa using mul_le_mul_of_nonneg_left hsq hC.le
  refine ⟨fun L => (hle L).trans_eq (hform L), ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ))) htend hqnonneg hle

end QI

