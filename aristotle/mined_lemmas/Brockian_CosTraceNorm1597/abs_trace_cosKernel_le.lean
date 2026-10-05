/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- because Lean 4 requires all `import` commands to precede any command, including a module
-- docstring. The identical text is repeated below as the module docstring.)

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (f i - g j)`. -/

theorem abs_trace_cosKernel_le {n : ℕ} (f g : Fin n → ℝ) :
    |(cosKernel f g).trace| ≤ (n : ℝ) := by
  classical
  have h : (cosKernel f g).trace = ∑ i, Real.cos (f i - g i) := rfl
  rw [h]
  calc |∑ i, Real.cos (f i - g i)| ≤ ∑ i : Fin n, |Real.cos (f i - g i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp

end Brockian

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

