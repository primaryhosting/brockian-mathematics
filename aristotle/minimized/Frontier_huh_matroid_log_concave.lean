import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede all other commands (including module
-- docstrings), so the required header comment appears immediately after the import.

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

namespace Frontier

open Polynomial Finset

/-- The characteristic polynomial of a matroid `M` on a finite ground set, defined by the
Whitney rank expression `χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`, where `r` is the
rank function of `M`. -/

theorem choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases le_or_gt n (k + 1) with h | h
  · have hz : n.choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz]
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + j + 2 := ⟨n - k - 2, by omega⟩
    have h1 := Nat.choose_succ_right_eq (k + j + 2) k
    have h2 := Nat.choose_succ_right_eq (k + j + 2) (k + 1)
    have e1 : k + j + 2 - k = j + 2 := by omega
    have e2 : k + j + 2 - (k + 1) = j + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    set a := (k + j + 2).choose k with ha
    set b := (k + j + 2).choose (k + 1) with hb
    set c := (k + j + 2).choose (k + 2) with hc
    have key : (a * c) * ((j + 2) * (k + 2)) = b ^ 2 * ((k + 1) * (j + 1)) :=
      calc (a * c) * ((j + 2) * (k + 2)) = (a * (j + 2)) * (c * (k + 1 + 1)) := by ring
        _ = (b * (k + 1)) * (b * (j + 1)) := by rw [← h1, h2]
        _ = b ^ 2 * ((k + 1) * (j + 1)) := by ring
    have hle : b ^ 2 * ((k + 1) * (j + 1)) ≤ b ^ 2 * ((j + 2) * (k + 2)) := by
      apply Nat.mul_le_mul_left
      nlinarith
    exact Nat.le_of_mul_le_mul_right (key ▸ hle) (by positivity)

/-- Coefficients of `(X - 1) ^ n` in `ℤ[X]`. -/
