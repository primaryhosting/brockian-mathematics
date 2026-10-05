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
