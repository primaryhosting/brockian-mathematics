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

