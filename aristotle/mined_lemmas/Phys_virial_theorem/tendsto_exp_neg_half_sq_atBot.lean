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

theorem tendsto_exp_neg_half_sq_atBot :
    Tendsto (fun x : ℝ => Real.exp (-x ^ 2 / 2)) atBot (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atBot atTop := by
    apply Filter.Tendsto.atTop_div_const (by norm_num)
    exact tendsto_pow_atBot_atTop_of_even (by decide)
  exact (tendsto_neg_atBot_iff.mpr h1).congr fun x => by ring

/-- `xⁿ exp (-x²) → 0` at `+∞`. -/
