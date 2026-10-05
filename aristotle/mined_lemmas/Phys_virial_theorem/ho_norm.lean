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

theorem ho_norm : ∫ x : ℝ, (hoPsi x) ^ 2 = 1 := by
  have hgauss : ∫ x : ℝ, Real.exp (-1 * x ^ 2) = Real.sqrt (Real.pi / 1) := integral_gaussian 1
  have hfun : (fun x : ℝ => (hoPsi x) ^ 2) = fun x : ℝ => hoC ^ 2 * Real.exp (-1 * x ^ 2) := by
    funext x
    rw [hoPsi, mul_pow, exp_neg_half_sq_sq]
    ring_nf
  rw [hfun, integral_const_mul, hgauss, hoC_sq]
  rw [div_one]
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

/-- Integrability of `c • xⁿ exp (-x²)` written in whatever algebraic shape is needed. -/
