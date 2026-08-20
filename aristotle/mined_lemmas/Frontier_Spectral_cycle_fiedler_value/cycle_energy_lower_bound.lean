/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as a plain block comment; its text is verbatim.)

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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Complex ZMod Matrix

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian matrix of the cycle graph `C n`, with vertex set `ZMod n`:
`2` on the diagonal, `-1` between neighbours `i` and `i ± 1`, `0` elsewhere. -/

lemma cycle_energy_lower_bound {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℂ)
    (h0 : ∑ j, x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j, ‖x j‖ ^ 2 ≤ ∑ j, ‖x j - x (j + 1)‖ ^ 2 := by
  set mu := 2 - 2 * Real.cos (2 * Real.pi / n) with hmu
  have hpar1 := dftAux_parseval x
  have hpar2 := dftAux_parseval (fun j => x j - x (j + 1))
  have hterm : ∀ k : ZMod n,
      mu * ‖dftAux n x k‖ ^ 2 ≤ ‖dftAux n (fun j => x j - x (j + 1)) k‖ ^ 2 := by
    intro k
    rw [dftAux_shift, norm_mul, mul_pow, norm_one_sub_stdAddChar_sq]
    by_cases hk : k = 0
    · have hz : dftAux n x k = 0 := by rw [hk, dftAux_zero, h0]
      simp [hz]
    · have hnk : (-k) ≠ 0 := neg_ne_zero.mpr hk
      have hv1 : 1 ≤ (-k).val ∧ (-k).val ≤ n - 1 := by
        have h1 : (-k).val < n := ZMod.val_lt _
        have h2 : (-k).val ≠ 0 := fun hh => hnk ((ZMod.val_eq_zero _).mp hh)
        omega
      have hcos := cos_le_cos_two_pi_div n (-k).val hv1.1 hv1.2 hn
      have hnn : (0:ℝ) ≤ ‖dftAux n x k‖ ^ 2 := sq_nonneg _
      have hle : mu ≤ 2 - 2 * Real.cos (2 * Real.pi * (-k).val / n) := by
        simp only [hmu]; linarith
      exact mul_le_mul_of_nonneg_right hle hnn
  have hsum : mu * ∑ k : ZMod n, ‖dftAux n x k‖ ^ 2
      ≤ ∑ k : ZMod n, ‖dftAux n (fun j => x j - x (j + 1)) k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hterm k)
  rw [hpar1, hpar2] at hsum
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  nlinarith [hsum]

/-- Real form of the spectral lower bound. -/
