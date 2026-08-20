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

theorem hermiteP_deg_coeff (n : ℕ) :
    (hermiteP n).natDegree ≤ n ∧ (hermiteP n).coeff n = 2 ^ n := by
  induction n with
  | zero => refine ⟨by simp [hermiteP], by simp [hermiteP]⟩
  | succ n ih =>
      obtain ⟨hdeg, hco⟩ := ih
      have hsucc : hermiteP (n + 1) = 2 * X * hermiteP n - derivative (hermiteP n) := rfl
      have hd1 : (2 * X * hermiteP n).natDegree ≤ n + 1 := by
        calc (2 * X * hermiteP n).natDegree
            ≤ (2 * X : ℝ[X]).natDegree + (hermiteP n).natDegree := natDegree_mul_le
          _ ≤ 1 + n := by
              gcongr
              exact le_trans natDegree_mul_le (by simp)
          _ = n + 1 := by ring
      have hd2 : (derivative (hermiteP n)).natDegree ≤ n + 1 :=
        le_trans (natDegree_derivative_le _) (by omega)
      refine ⟨le_trans (natDegree_sub_le _ _) (max_le hd1 hd2), ?_⟩
      rw [hsucc, coeff_sub, coeff_derivative]
      have h0 : (hermiteP n).coeff (n + 1 + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have h1 : (2 * X * hermiteP n).coeff (n + 1) = 2 * (hermiteP n).coeff n := by
        rw [mul_assoc, mul_comm (2 : ℝ[X]), mul_assoc]
        simp [mul_comm]
      rw [h0, h1, hco]
      ring

