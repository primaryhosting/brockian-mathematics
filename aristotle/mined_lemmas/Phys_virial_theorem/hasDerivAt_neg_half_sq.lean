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

theorem hasDerivAt_neg_half_sq (x : ℝ) : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-x) x := by
  have h := ((hasDerivAt_id x).pow 2).neg.div_const 2
  refine h.congr_deriv ?_
  simp
  ring

