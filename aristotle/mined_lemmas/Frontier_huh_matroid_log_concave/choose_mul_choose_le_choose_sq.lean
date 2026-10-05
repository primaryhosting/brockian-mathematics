import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

theorem choose_mul_choose_le_choose_sq (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
  set a := n.choose k with ha
  set b := n.choose (k + 1) with hb
  set c := n.choose (k + 2) with hc
  have h1 : b * (k + 1) = a * (n - k) := Nat.choose_succ_right_eq n k
  have h2 : c * (k + 2) = b * (n - (k + 1)) := Nat.choose_succ_right_eq n (k + 1)
  have key : (k + 1) * (n - (k + 1)) ≤ (n - k) * (k + 2) := by
    by_cases h : n ≤ k
    · simp [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (h.trans (Nat.le_succ k))]
    · obtain ⟨d, hd⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
      subst hd
      have e : k + 1 + d - k = d + 1 := by omega
      rw [e]
      simp only [Nat.add_sub_cancel_left]
      nlinarith
  have e1 : a * c * ((k + 1) * (k + 2)) = a * b * ((k + 1) * (n - (k + 1))) := by
    calc a * c * ((k + 1) * (k + 2)) = a * (c * (k + 2)) * (k + 1) := by ring
      _ = a * (b * (n - (k + 1))) * (k + 1) := by rw [h2]
      _ = a * b * ((k + 1) * (n - (k + 1))) := by ring
  have e2 : b ^ 2 * ((k + 1) * (k + 2)) = a * b * ((n - k) * (k + 2)) := by
    calc b ^ 2 * ((k + 1) * (k + 2)) = (b * (k + 1)) * b * (k + 2) := by ring
      _ = (a * (n - k)) * b * (k + 2) := by rw [h1]
      _ = a * b * ((n - k) * (k + 2)) := by ring
  have hle : a * c * ((k + 1) * (k + 2)) ≤ b ^ 2 * ((k + 1) * (k + 2)) := by
    rw [e1, e2]; exact Nat.mul_le_mul_left _ key
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

/-- The coefficients of `(X - 1)^n` are the signed binomial coefficients. -/
