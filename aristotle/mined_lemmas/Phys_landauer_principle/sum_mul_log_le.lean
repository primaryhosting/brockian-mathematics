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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module doc-comment, so the header
-- above is repeated as the module documentation just after the import.)
import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Shannon entropy of a finite distribution (in nats) -/

/-- Shannon entropy (in nats) of a distribution `p` on a finite type,
using the standard convention `0 * log 0 = 0`. -/

theorem sum_mul_log_le {α : Type*} [Fintype α] (q m : α → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (hm0 : ∀ x, 0 ≤ m x)
    (hq1 : ∑ x, q x = 1) (hm1 : ∑ x, m x ≤ 1)
    (hac : ∀ x, q x ≠ 0 → m x ≠ 0) :
    ∑ x, q x * Real.log (m x) ≤ ∑ x, q x * Real.log (q x) := by
  have key : ∀ x : α, q x * Real.log (m x) - q x * Real.log (q x) ≤ m x - q x := by
    intro x
    rcases eq_or_lt_of_le (hq0 x) with h | h
    · simp [← h, hm0 x]
    · have hmx : 0 < m x := lt_of_le_of_ne (hm0 x) (fun hh => hac x h.ne' hh.symm)
      have hlog : Real.log (m x / q x) ≤ m x / q x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hmx h)
      rw [Real.log_div hmx.ne' h.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h.le
      calc q x * Real.log (m x) - q x * Real.log (q x)
          = q x * (Real.log (m x) - Real.log (q x)) := by ring
        _ ≤ q x * (m x / q x - 1) := hmul
        _ = m x - q x := by field_simp
  have hsum : ∑ x, (q x * Real.log (m x) - q x * Real.log (q x)) ≤ ∑ x, (m x - q x) :=
    Finset.sum_le_sum (fun x _ => key x)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq1] at hsum
  linarith

/-! ## Entropy computations -/

/-- A memory holding exactly one unpredictable bit has entropy `log 2`. -/
