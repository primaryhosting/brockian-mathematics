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

open Finset

-- Everything lives in this namespace so that `fourier` refers to the discrete Fourier
-- transform defined below rather than to Mathlib's `fourier` on `AddCircle`.
namespace CharacterSums

variable {q : ℕ} [NeZero q]

/-- The (unnormalised) discrete Fourier transform on `ZMod q`. -/

theorem sub_mean_le_of_fourier_bound_sharp (f : ZMod q → ℂ) (B : ℝ)
    (hB : ∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B) (x : ZMod q) :
    ‖f x - (q : ℂ)⁻¹ * fourier f 0‖ ≤ (q : ℝ)⁻¹ * ((q - 1 : ℕ) * B) := by
  have hsplit : ∑ a : ZMod q, ZMod.stdAddChar (a * x) * fourier f a
      = fourier f 0 + ∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod q))]
    simp
  have hkey : f x - (q : ℂ)⁻¹ * fourier f 0
      = (q : ℂ)⁻¹ * ∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a := by
    rw [fourier_inversion f x, hsplit, mul_add]
    ring
  have hsum : ‖∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a‖
      ≤ (q - 1 : ℕ) * B := by
    calc ‖∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a‖
        ≤ ∑ a ∈ univ.erase (0 : ZMod q), ‖ZMod.stdAddChar (a * x) * fourier f a‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a ∈ univ.erase (0 : ZMod q), B := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [norm_mul, norm_stdAddChar, one_mul]
          exact hB a (Finset.ne_of_mem_erase ha)
      _ = (q - 1 : ℕ) * B := by
          rw [Finset.sum_const, card_erase_zero, nsmul_eq_mul]
  rw [hkey, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/--
The statement originally requested,

```
