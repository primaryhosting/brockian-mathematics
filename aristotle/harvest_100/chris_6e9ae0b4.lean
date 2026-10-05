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
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- The uniform distribution on one bit: the memory before erasure. -/
noncomputable def uniformBit : Bool → ℝ := fun _ => 1 / 2

/-- The deterministic ("reset to `false`") distribution on one bit:
the memory after erasure. -/
noncomputable def erasedBit : Bool → ℝ := fun b => if b = false then 1 else 0

@[simp] lemma shannonEntropy_uniformBit : shannonEntropy uniformBit = Real.log 2 := by
  have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  simp only [shannonEntropy, uniformBit, Fintype.sum_bool, h2]
  ring

@[simp] lemma shannonEntropy_erasedBit : shannonEntropy erasedBit = 0 := by
  simp [shannonEntropy, erasedBit]

/-- Erasing one bit of memory reduces the Shannon entropy of the memory by exactly
`log 2` (one bit). -/
lemma entropy_drop_of_erasure :
    shannonEntropy uniformBit - shannonEntropy erasedBit = Real.log 2 := by
  simp

/-- **Gibbs' inequality for one bit**: no distribution on a two-state memory carries
more than `log 2` of entropy, so `log 2` is exactly the information content of one bit. -/
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
theorem landauer_bound_of_entropy_balance {α : Type*} [Fintype α] (p q : α → ℝ)
    (k T Q σ : ℝ) (hk : 0 < k) (hT : 0 < T) (hσ : 0 ≤ σ)
    (hbalance : σ = (shannonEntropy q - shannonEntropy p) + Q / (k * T)) :
    k * T * (shannonEntropy p - shannonEntropy q) ≤ Q := by
  have hkT : 0 < k * T := mul_pos hk hT
  have h : shannonEntropy p - shannonEntropy q ≤ Q / (k * T) := by linarith
  calc k * T * (shannonEntropy p - shannonEntropy q) ≤ k * T * (Q / (k * T)) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hkT)
    _ = Q := by field_simp

/-- **Landauer's principle.**  Erasing one bit of information — resetting a memory that is
uniformly distributed over its two states to the definite state `false` — while in contact with
a heat bath at absolute temperature `T > 0` dissipates at least `k T log 2` of heat.

The only physical input is the second law of thermodynamics, in the form that the total entropy
production `σ = ΔS_memory + Q / (k T)` of the process is nonnegative; the bound
`Q ≥ k T log 2` is then derived, the value `log 2` being the exact entropy content of one bit. -/
theorem landauer_principle (k T Q σ : ℝ) (hk : 0 < k) (hT : 0 < T) (hσ : 0 ≤ σ)
    (hbalance : σ = (shannonEntropy erasedBit - shannonEntropy uniformBit) + Q / (k * T)) :
    k * T * Real.log 2 ≤ Q := by
  have h := landauer_bound_of_entropy_balance uniformBit erasedBit k T Q σ hk hT hσ hbalance
  rwa [entropy_drop_of_erasure] at h

/-- **Landauer's principle for an arbitrary initial memory state.**  Resetting a one-bit memory
with arbitrary initial distribution `p` to the definite state `false` dissipates at least
`k T S(p)` of heat, and this quantity never exceeds `k T log 2`: the erasure cost is maximal
when the bit is initially unbiased. -/
theorem landauer_principle_of_initial_state (p : Bool → ℝ) (h0 : ∀ b, 0 ≤ p b)
    (hsum : p false + p true = 1) (k T Q σ : ℝ) (hk : 0 < k) (hT : 0 < T) (hσ : 0 ≤ σ)
    (hbalance : σ = (shannonEntropy erasedBit - shannonEntropy p) + Q / (k * T)) :
    k * T * shannonEntropy p ≤ Q ∧ k * T * shannonEntropy p ≤ k * T * Real.log 2 := by
  have h := landauer_bound_of_entropy_balance p erasedBit k T Q σ hk hT hσ hbalance
  rw [shannonEntropy_erasedBit, sub_zero] at h
  refine ⟨h, ?_⟩
  exact mul_le_mul_of_nonneg_left (shannonEntropy_bool_le_log_two p h0 hsum)
    (le_of_lt (mul_pos hk hT))

/-- The Landauer bound is sharp: a reversible erasure (zero entropy production) releases
exactly `k T log 2` of heat, so no larger lower bound is possible. -/
theorem landauer_principle_sharp (k T : ℝ) (hk : 0 < k) (hT : 0 < T) :
    ∃ Q σ : ℝ, 0 ≤ σ ∧
      σ = (shannonEntropy erasedBit - shannonEntropy uniformBit) + Q / (k * T) ∧
      Q = k * T * Real.log 2 := by
  refine ⟨k * T * Real.log 2, 0, le_refl 0, ?_, rfl⟩
  have hkT : (k * T) ≠ 0 := ne_of_gt (mul_pos hk hT)
  field_simp
  rw [shannonEntropy_erasedBit, shannonEntropy_uniformBit]
  ring

end Phys

