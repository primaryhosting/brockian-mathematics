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

theorem sub_mean_le_of_fourier_bound (f : ZMod q → ℂ) (B : ℝ)
    (hB : ∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B) (x : ZMod q) :
    ‖f x - (q : ℂ)⁻¹ * fourier f 0‖ ≤ (q - 1 : ℕ) * B := by
  refine (sub_mean_le_of_fourier_bound_sharp f B hB x).trans ?_
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) with h1 | h2
  · simp [← h1]
  · have : Fact (1 < q) := ⟨h2⟩
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 one_ne_zero)
    have hq1 : (q : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact mul_le_of_le_one_left (by positivity) hq1

end CharacterSums

