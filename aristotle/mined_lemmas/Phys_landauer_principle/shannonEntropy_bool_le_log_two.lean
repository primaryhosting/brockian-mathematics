/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability distribution `p`. -/

lemma shannonEntropy_bool_le_log_two (p : Bool → ℝ) (h0 : ∀ b, 0 ≤ p b)
    (hsum : p false + p true = 1) : shannonEntropy p ≤ Real.log 2 := by
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → -(x * Real.log x) ≤ x * Real.log 2 + (1 / 2 - x) := by
    intro x hx _
    rcases eq_or_lt_of_le hx with h | hx'
    · rw [← h]; norm_num
    · have hlog : Real.log (1 / (2 * x)) ≤ 1 / (2 * x) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hmul : x * Real.log (1 / (2 * x)) ≤ x * (1 / (2 * x) - 1) := by
        exact mul_le_mul_of_nonneg_left hlog hx
      have hexp : Real.log (1 / (2 * x)) = -(Real.log 2) - Real.log x := by
        rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hx')]
        ring
      have hx2 : x * (1 / (2 * x) - 1) = 1 / 2 - x := by
        field_simp
      rw [hexp, hx2] at hmul
      nlinarith [hmul]
  have hf := key (p false) (h0 false) (by nlinarith [h0 true])
  have ht := key (p true) (h0 true) (by nlinarith [h0 false])
  have hsplit :
      shannonEntropy p = -(p false * Real.log (p false)) + -(p true * Real.log (p true)) := by
    simp [shannonEntropy]
  have hlog : p false * Real.log 2 + p true * Real.log 2 = Real.log 2 := by
    rw [← add_mul, hsum, one_mul]
  rw [hsplit]
  linarith [hf, ht]

/-- **Generalized Landauer bound.**  Suppose a memory in state distribution `p` is driven to
state distribution `q` while in contact with a heat bath at absolute temperature `T > 0`
(Boltzmann constant `k > 0`), releasing heat `Q` into the bath.  The second law of
thermodynamics says the total entropy production
`σ = ΔS_memory + Q / (k T)` (in units of `k`) is nonnegative.  Then the heat released is at
least `k T` times the entropy decrease of the memory. -/
