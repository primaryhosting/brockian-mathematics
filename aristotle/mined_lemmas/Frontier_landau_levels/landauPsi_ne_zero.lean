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

theorem landauPsi_ne_zero (hbar q B k : ℝ) (n : ℕ) (hhbar : 0 < hbar) (hqB : 0 < q * B) :
    landauPsi hbar q B n k ≠ 0 := by
  obtain ⟨t, ht⟩ := oscFun_ne_zero n
  have hcpos : 0 < Real.sqrt (q * B / hbar) := Real.sqrt_pos.mpr (div_pos hqB hhbar)
  have hc0 : Real.sqrt (q * B / hbar) ≠ 0 := ne_of_gt hcpos
  intro h
  have h0 : landauPsi hbar q B n k
      (t / Real.sqrt (q * B / hbar) + hbar * k / (q * B)) 0 = 0 := by rw [h]; rfl
  rw [landauPsi] at h0
  have harg : Real.sqrt (q * B / hbar) *
      (t / Real.sqrt (q * B / hbar) + hbar * k / (q * B) - hbar * k / (q * B)) = t := by
    field_simp
    ring
  rw [harg] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Complex.exp_ne_zero _ h1
  · exact ht (by exact_mod_cast h1)

end Frontier

