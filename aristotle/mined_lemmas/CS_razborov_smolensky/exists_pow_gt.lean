import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem exists_pow_gt (A B : ℕ) : ∃ ℓ : ℕ, 1 ≤ ℓ ∧ A * (ℓ + 1) ^ B < 2 ^ ℓ := by
  have hlo : (fun n : ℕ => ((n : ℝ)) ^ B) =o[Filter.atTop] (fun n : ℕ => (2 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt B (by norm_num)
  have hC : (0:ℝ) < (A : ℝ) * 2 ^ B + 1 := by positivity
  have hev := (hlo.def' (by positivity : (0:ℝ) < 1 / ((A : ℝ) * 2 ^ B + 1))).bound
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  set ℓ := max N 1 with hℓ
  have h1 : N ≤ ℓ := le_max_left _ _
  have h2 : 1 ≤ ℓ := le_max_right _ _
  have hmain := hN ℓ h1
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((ℓ:ℝ)) ^ B),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ) ^ ℓ)] at hmain
  -- convert to naturals
  have hcast : ((A * (ℓ + 1) ^ B : ℕ) : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by
    push_cast
    have hle : ((ℓ : ℝ) + 1) ^ B ≤ 2 ^ B * (ℓ : ℝ) ^ B := by
      rw [← mul_pow]
      have h1l : (1:ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h2
      refine pow_le_pow_left₀ (by positivity) (by linarith) B
    calc (A : ℝ) * ((ℓ : ℝ) + 1) ^ B ≤ (A : ℝ) * (2 ^ B * (ℓ : ℝ) ^ B) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((A : ℝ) * 2 ^ B) * (ℓ : ℝ) ^ B := by ring
      _ ≤ ((A : ℝ) * 2 ^ B) * (1 / ((A : ℝ) * 2 ^ B + 1) * (2:ℝ) ^ ℓ) := by
          exact mul_le_mul_of_nonneg_left hmain (by positivity)
      _ < (2:ℝ) ^ ℓ := by
          have hp : (0:ℝ) < (2:ℝ) ^ ℓ := by positivity
          have hKpos : (0:ℝ) < (A : ℝ) * 2 ^ B + 1 := hC
          rw [show ((A : ℝ) * 2 ^ B) * (1 / ((A : ℝ) * 2 ^ B + 1) * (2:ℝ) ^ ℓ)
              = (((A : ℝ) * 2 ^ B) / ((A : ℝ) * 2 ^ B + 1)) * (2:ℝ) ^ ℓ by ring]
          have hlt : ((A : ℝ) * 2 ^ B) / ((A : ℝ) * 2 ^ B + 1) < 1 := by
            rw [div_lt_one hKpos]; linarith
          nlinarith
  exact_mod_cast hcast

end CS

import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# Razborov–Smolensky approximation

Every `AC⁰[q]` circuit of depth `d` and size `s` is approximated, on all but a
`s · 2⁻ˡ` fraction of the inputs, by a function of degree at most `(ℓ (q-1))^d`
over a field of characteristic `q`.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-! ### Elementary facts -/

