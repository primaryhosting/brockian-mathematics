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
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization

We formalize the standard *concatenated-code* form of the quantum threshold theorem.

Fix a constant error threshold `pth > 0` coming from a fault-tolerant gate gadget: one level
of code concatenation replaces a physical failure probability `q` by the logical failure
probability `q ^ 2 / pth` (the gadget fails only if at least two of its constituent blocks
fail, and `pth` is the inverse of the number of malignant pairs of fault locations).

`QI.logicalError pth p L` is the failure probability after `L` levels of concatenation,
starting from physical error rate `p`.

The threshold theorem, `QI.threshold_theorem`, says: **if the physical error rate is strictly
below the threshold, then arbitrarily accurate computation is possible**, i.e. for every target
accuracy `ε > 0` there is a concatenation level `L₀` such that every level `L ≥ L₀` achieves
logical error rate `< ε`.  Equivalently (`QI.logicalError_tendsto_zero`) the logical error rate
tends to `0`; the doubly-exponential rate of convergence is recorded in
`QI.logicalError_eq` : `logicalError pth p L = pth * (p / pth) ^ (2 ^ L)`.
-/

namespace QI

/-- Logical error rate after `L` levels of concatenation of a fault-tolerant code with
error threshold `pth`, starting from physical error rate `p`.  One level of concatenation
maps an error rate `q` to `q ^ 2 / pth`. -/
noncomputable def logicalError (pth p : ℝ) : ℕ → ℝ
  | 0 => p
  | L + 1 => (logicalError pth p L) ^ 2 / pth

@[simp] theorem logicalError_zero (pth p : ℝ) : logicalError pth p 0 = p := rfl

@[simp] theorem logicalError_succ (pth p : ℝ) (L : ℕ) :
    logicalError pth p (L + 1) = (logicalError pth p L) ^ 2 / pth := rfl

/-- Closed form for the logical error rate: it decays doubly exponentially in the
concatenation level. -/
theorem logicalError_eq (pth p : ℝ) (hpth : 0 < pth) (L : ℕ) :
    logicalError pth p L = pth * (p / pth) ^ (2 ^ L) := by
  induction L with
  | zero => simp [mul_div_cancel₀, hpth.ne']
  | succ L ih =>
      rw [logicalError_succ, ih, pow_succ 2 L, pow_mul]
      field_simp

/-- Nonnegativity of the logical error rate. -/
theorem logicalError_nonneg {pth p : ℝ} (hpth : 0 < pth) (hp : 0 ≤ p) (L : ℕ) :
    0 ≤ logicalError pth p L := by
  rw [logicalError_eq pth p hpth]
  exact mul_nonneg hpth.le (pow_nonneg (div_nonneg hp hpth.le) _)

/-- Below threshold, the logical error rate is bounded by a geometric sequence. -/
theorem logicalError_le_geometric {pth p : ℝ} (hpth : 0 < pth) (hp : 0 ≤ p) (hlt : p < pth)
    (L : ℕ) : logicalError pth p L ≤ pth * (p / pth) ^ L := by
  have hr0 : 0 ≤ p / pth := div_nonneg hp hpth.le
  have hr1 : p / pth ≤ 1 := (div_le_one hpth).2 hlt.le
  rw [logicalError_eq pth p hpth]
  have : (p / pth) ^ (2 ^ L) ≤ (p / pth) ^ L :=
    pow_le_pow_of_le_one hr0 hr1 (Nat.le_of_lt_succ (Nat.lt_two_pow_self.trans (Nat.lt_succ_self _)))
  exact mul_le_mul_of_nonneg_left this hpth.le

/-- Below threshold, the logical error rate tends to `0` as the number of concatenation
levels grows. -/
theorem logicalError_tendsto_zero {pth p : ℝ} (hpth : 0 < pth) (hp : 0 ≤ p) (hlt : p < pth) :
    Filter.Tendsto (logicalError pth p) Filter.atTop (nhds 0) := by
  have hr0 : 0 ≤ p / pth := div_nonneg hp hpth.le
  have hr1 : p / pth < 1 := (div_lt_one hpth).2 hlt
  have hgeom : Filter.Tendsto (fun L : ℕ => pth * (p / pth) ^ L) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul pth
    simpa using this
  exact squeeze_zero (fun L => logicalError_nonneg hpth hp L)
    (fun L => logicalError_le_geometric hpth hp hlt L) hgeom

/-- **Threshold theorem.**  If the physical error rate `p` lies strictly below the constant
error threshold `pth`, then fault-tolerant quantum computation is possible to arbitrary
accuracy: for every target error `ε > 0` there is a concatenation level `L₀` such that
encoding with any number of levels `L ≥ L₀` yields logical error rate below `ε`. -/
theorem threshold_theorem {pth p : ℝ} (hpth : 0 < pth) (hp : 0 ≤ p) (hlt : p < pth)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, logicalError pth p L < ε := by
  have h := logicalError_tendsto_zero hpth hp hlt
  have := (h.eventually (eventually_lt_nhds hε)).exists_forall_of_atTop
  simpa using this

end QI

