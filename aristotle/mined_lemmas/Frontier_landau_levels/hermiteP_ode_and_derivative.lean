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

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/

theorem hermiteP_ode_and_derivative (n : ℕ) :
    derivative (derivative (hermiteP n)) - 2 * X * derivative (hermiteP n)
        + 2 * (n : ℝ[X]) * hermiteP n = 0 ∧
      derivative (hermiteP (n + 1)) = 2 * ((n : ℝ[X]) + 1) * hermiteP n := by
  induction n with
  | zero => refine ⟨by simp [hermiteP], by simp [hermiteP, derivative_mul]⟩
  | succ n ih =>
      obtain ⟨-, hd⟩ := ih
      have hsucc : hermiteP (n + 1) = 2 * X * hermiteP n - derivative (hermiteP n) := rfl
      have hB : derivative (derivative (hermiteP (n + 1)))
          - 2 * X * derivative (hermiteP (n + 1)) + 2 * ((n : ℝ[X]) + 1) * hermiteP (n + 1) = 0 := by
        rw [hd, hsucc]
        simp [derivative_mul, mul_sub, mul_add, add_mul]
        ring
      refine ⟨by push_cast; linear_combination hB, ?_⟩
      have hsucc2 :
          hermiteP (n + 1 + 1) = 2 * X * hermiteP (n + 1) - derivative (hermiteP (n + 1)) := rfl
      rw [hsucc2, derivative_sub, derivative_mul, derivative_mul]
      push_cast
      simp only [derivative_ofNat, derivative_X, zero_mul, mul_one, zero_add]
      linear_combination -hB

