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

theorem mutualInfo_eq_sum_klDiv (p : I → ℝ) (Q : I → Y → ℝ) (hQ1 : ∀ i, ∑ y, Q i y = 1) :
    mutualInfo (fun i y => p i * Q i y)
      = ∑ i, p i * klDiv (Q i) (fun y => ∑ j, p j * Q j y) := by
  unfold mutualInfo klDiv
  apply Finset.sum_congr rfl
  intro i _
  have hrow : ∑ y', p i * Q i y' = p i := by rw [← Finset.mul_sum, hQ1 i, mul_one]
  simp only [hrow]
  rcases eq_or_ne (p i) 0 with h0 | h0
  · simp [h0]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [mul_div_mul_left _ _ h0]
    ring

/-- The Holevo bound for a classical ensemble measured through a stochastic channel:
the mutual information between the label and the outcome is at most the χ quantity. -/
