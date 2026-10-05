/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical information quantities -/

section ClassicalDefs

variable {X I Y : Type*}

/-- Shannon entropy `H(P) = -∑ P x * log (P x)` of a finite probability vector. -/

theorem klDiv_channel_le (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hab : ∀ x, b x = 0 → a x = 0) (M : X → Y → ℝ) (hM : ∀ x y, 0 ≤ M x y)
    (hM1 : ∀ x, ∑ y, M x y = 1) :
    klDiv (fun y => ∑ x, a x * M x y) (fun y => ∑ x, b x * M x y) ≤ klDiv a b := by
  have step1 : klDiv (fun y => ∑ x, a x * M x y) (fun y => ∑ x, b x * M x y)
      ≤ ∑ y, ∑ x, (a x * M x y) * Real.log ((a x * M x y) / (b x * M x y)) := by
    apply Finset.sum_le_sum
    intro y _
    exact log_sum_inequality (fun x => a x * M x y) (fun x => b x * M x y)
      (fun x => mul_nonneg (ha x) (hM x y)) (fun x => mul_nonneg (hb x) (hM x y))
      (fun x hx => by
        simp only at hx ⊢
        rcases mul_eq_zero.mp hx with h | h
        · rw [hab x h]; ring
        · rw [h]; ring)
  have step2 : ∀ x, ∑ y, (a x * M x y) * Real.log ((a x * M x y) / (b x * M x y))
      = a x * Real.log (a x / b x) := by
    intro x
    have hterm : ∀ y ∈ Finset.univ, (a x * M x y) * Real.log ((a x * M x y) / (b x * M x y))
        = (M x y) * (a x * Real.log (a x / b x)) := by
      intro y _
      rcases eq_or_lt_of_le (hM x y) with h | h
      · simp [← h]
      · rw [mul_div_mul_right _ _ (ne_of_gt h)]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hM1 x, one_mul]
  rw [Finset.sum_comm] at step1
  simp only [step2] at step1
  exact step1

