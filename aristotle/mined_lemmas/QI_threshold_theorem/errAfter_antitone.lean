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

/-- `errAfter C p L` is the logical error rate of a gate location after `L` levels of
code concatenation, in the standard fault-tolerance recursion: one level of encoding
turns a physical error rate `q` into a logical error rate `C * q ^ 2`, where `C` counts
the number of pairs of fault locations in one level-1 rectangle. -/

lemma errAfter_antitone {C p : ℝ} (hC : 0 < C) (hp : 0 ≤ p) (hlt : C * p ≤ 1)
    {L M : ℕ} (hLM : L ≤ M) : errAfter C p M ≤ errAfter C p L := by
  rw [errAfter_closed_form hC p L, errAfter_closed_form hC p M]
  have hCp : 0 ≤ C * p := by positivity
  have hpow : (C * p) ^ (2 ^ M) ≤ (C * p) ^ (2 ^ L) :=
    pow_le_pow_of_le_one hCp hlt (Nat.pow_le_pow_right (by norm_num) hLM)
  have : (0:ℝ) < 1 / C := by positivity
  exact mul_le_mul_of_nonneg_left hpow this.le

/-- Existence of a concatenation level whose (dyadic) size exceeds a given bound,
together with the doubling control on the least such level. -/
