/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

set_option grind.warning false

namespace QI

open Finset

/-- The number of inputs `x` on which the oracle `f` returns `true`. -/

lemma djOutput_zero {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djOutput f (fun _ => false) = amplitude f := by
  have hc : ((Real.sqrt 2) ^ n)⁻¹ * ((Real.sqrt 2) ^ n)⁻¹ = (1 / 2 ^ n : ℝ) := by
    rw [← mul_inv, ← mul_pow, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), one_div]
  unfold djOutput
  rw [hadamardAll_zeroState]
  simp only [hadamardAll, oraclePhase, dotSign_zero_right, one_mul, amplitude,
    ← Finset.sum_mul, ← mul_assoc]
  rw [mul_right_comm, hc]

/-- **Deutsch–Jozsa.** With a single query to the oracle for `f`, the amplitude
`2⁻ⁿ ∑ₓ (-1)^{f(x)}` of the all-zeros outcome distinguishes the two promises:
it has modulus `1` when `f` is constant (the all-zeros outcome occurs with
probability one) and is `0` when `f` is balanced (the all-zeros outcome never
occurs). Hence one measurement decides constant vs. balanced. -/
