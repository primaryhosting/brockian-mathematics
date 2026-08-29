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

theorem sum_klDiv_eq_entropy_sub (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (P : I → X → ℝ) (hP : ∀ i x, 0 ≤ P i x) :
    ∑ i, p i * klDiv (P i) (fun x => ∑ j, p j * P j x)
      = shannonEntropy (fun x => ∑ j, p j * P j x) - ∑ i, p i * shannonEntropy (P i) := by
  set Pb : X → ℝ := fun x => ∑ j, p j * P j x with hPb
  have key : ∀ i, p i * klDiv (P i) Pb
      = p i * (∑ x, P i x * Real.log (P i x)) - ∑ x, p i * P i x * Real.log (Pb x) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · simp [← h0]
    · have hk : klDiv (P i) Pb = ∑ x, (P i x * Real.log (P i x) - P i x * Real.log (Pb x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases eq_or_lt_of_le (hP i x) with hx | hx
        · simp [← hx]
        · have hbx : 0 < Pb x := by
            have : p i * P i x ≤ Pb x :=
              Finset.single_le_sum (f := fun j => p j * P j x)
                (fun j _ => mul_nonneg (hp j) (hP j x)) (Finset.mem_univ i)
            nlinarith
          rw [Real.log_div (ne_of_gt hx) (ne_of_gt hbx)]
          ring
      rw [hk, Finset.sum_sub_distrib, mul_sub]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib]
  have h1 : ∑ i, ∑ x, p i * P i x * Real.log (Pb x) = ∑ x, Pb x * Real.log (Pb x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => by rw [← Finset.sum_mul]
  have h2 : ∀ i, p i * (∑ x, P i x * Real.log (P i x)) = -(p i * shannonEntropy (P i)) := by
    intro i
    rw [shannonEntropy_eq_neg]
    ring
  rw [h1, shannonEntropy_eq_neg Pb, Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_neg_distrib]
  ring

/-- Mutual information of a joint distribution `J i y = p i * Q i y` as an average KL divergence. -/
