import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma relEntropy_channel_le {Z Y : Type*} [Fintype Z] [Fintype Y]
    (a b : Z → ℝ) (E : Y → Z → ℝ)
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hac : ∀ z, b z = 0 → a z = 0)
    (hE0 : ∀ y z, 0 ≤ E y z) (hE1 : ∀ z, ∑ y, E y z = 1) :
    ∑ y, (∑ z, a z * E y z) * Real.log ((∑ z, a z * E y z) / (∑ z, b z * E y z))
      ≤ ∑ z, a z * Real.log (a z / b z) := by
  have step : ∀ y : Y,
      (∑ z, a z * E y z) * Real.log ((∑ z, a z * E y z) / (∑ z, b z * E y z))
        ≤ ∑ z, E y z * (a z * Real.log (a z / b z)) := by
    intro y
    have h := log_sum_inequality (Finset.univ : Finset Z)
      (fun z => a z * E y z) (fun z => b z * E y z)
      (fun z _ => mul_nonneg (ha z) (hE0 y z))
      (fun z _ => mul_nonneg (hb z) (hE0 y z))
      (by
        intro z _ hz
        simp only at hz ⊢
        rcases mul_eq_zero.1 hz with h1 | h1
        · simp [hac z h1]
        · simp [h1])
    refine h.trans_eq ?_
    refine Finset.sum_congr rfl ?_
    intro z _
    show a z * E y z * Real.log (a z * E y z / (b z * E y z))
      = E y z * (a z * Real.log (a z / b z))
    rcases eq_or_lt_of_le (hE0 y z) with hE | hE
    · rw [← hE]; simp
    · rw [mul_div_mul_right _ _ hE.ne']; ring
  calc ∑ y, (∑ z, a z * E y z) * Real.log ((∑ z, a z * E y z) / (∑ z, b z * E y z))
      ≤ ∑ y, ∑ z, E y z * (a z * Real.log (a z / b z)) :=
        Finset.sum_le_sum (fun y _ => step y)
    _ = ∑ z, a z * Real.log (a z / b z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [← Finset.sum_mul, hE1 z, one_mul]

/-! ### The classical Holevo quantity -/

/-- The Holevo quantity of a classical ensemble equals the average relative entropy to the
average distribution. -/
