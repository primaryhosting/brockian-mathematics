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

theorem tendsto_of_eq_pow_mul_gaussian_atBot {f : ℝ → ℝ} (c : ℝ) (n : ℕ)
    (hf : ∀ x : ℝ, f x = c * (x ^ n * Real.exp (-x ^ 2))) : Tendsto f atBot (𝓝 0) := by
  have := (tendsto_pow_mul_gaussian_atBot n).const_mul c
  rw [mul_zero] at this
  exact this.congr fun x => (hf x).symm

/-- **Virial theorem for the harmonic-oscillator ground state.**  All hypotheses of
`Phys.virial_theorem` are verified for `ψ(x) = π^(-1/4) exp(-x²/2)`, `V(x) = x²/2`,
`E = 1/2`; in particular the hypotheses of the general theorem are consistent. -/
