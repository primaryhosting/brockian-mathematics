/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open intervalIntegral

/-- For a state `ψ t = exp (i θ t)` with real phase `θ`, the Berry connection
`A t = -i ⟨ψ t, dψ/dt⟩ = -i * conj (ψ t) * ψ' t` is exactly the rate of change `θ' t` of the
phase. Hence integrating `θ'` along the loop is integrating the Berry connection. -/

lemma berry_phase_eq_phase_difference
    (θ θ' : ℝ → ℝ) (hderiv : ∀ t, HasDerivAt θ (θ' t) t) (hcont : Continuous θ') :
    ∫ t in (0:ℝ)..1, θ' t = θ 1 - θ 0 := by
  exact integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 1)

/-- **Berry phase quantization.**

Consider a state `t ↦ exp (i θ t)` transported around a closed loop parametrized by `t ∈ [0,1]`,
whose phase `θ` varies at the continuous rate `θ'` (the Berry connection pulled back to the loop).
If the state returns to itself at the end of the loop (`exp (i θ 0) = exp (i θ 1)`), then the
Berry phase accumulated around the loop, `∫₀¹ θ' t dt`, is an integer multiple of `2π`. -/
