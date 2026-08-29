import RequestProject.Main

/-!
# A concrete instance of the virial theorem

The hypotheses of `Phys.virial_theorem` are satisfiable: we check them for the
ground state `ψ(x) = π^(-1/4) exp(-x²/2)` of the harmonic oscillator
`V(x) = x²/2`, with energy `E = 1/2`, and deduce the virial identity
`2⟨T⟩ = ⟨x ∂ₓV⟩ = 2⟨V⟩` for that state.
-/

namespace Phys

open MeasureTheory Filter Topology Real

/-- `exp (-x²/2)` squared is `exp (-x²)`. -/

theorem tendsto_pow_mul_gaussian_atBot (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have hbound : ∀ x : ℝ, ‖x ^ n * Real.exp (-x ^ 2)‖
      ≤ (1 + 2 ^ n * (Nat.factorial n : ℝ)) * Real.exp (-x ^ 2 / 2) := by
    intro x
    have h := abs_pow_mul_exp_neg_half_sq_le n x
    have hsplit : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hnorm : ‖x ^ n * Real.exp (-x ^ 2)‖
        = (|x| ^ n * Real.exp (-x ^ 2 / 2)) * Real.exp (-x ^ 2 / 2) := by
      rw [hsplit, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
        abs_of_pos (by positivity : (0:ℝ) < Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2))]
      ring
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hlim : Tendsto (fun x : ℝ => (1 + 2 ^ n * (Nat.factorial n : ℝ)) * Real.exp (-x ^ 2 / 2)) atBot (𝓝 0) := by
    simpa using tendsto_exp_neg_half_sq_atBot.const_mul (1 + 2 ^ n * (Nat.factorial n : ℝ))
  exact squeeze_zero_norm (fun x => hbound x) hlim

/-- Normalization constant `π^(-1/4)` of the harmonic-oscillator ground state. -/
