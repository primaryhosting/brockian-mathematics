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

lemma berry_connection_eq_phase_rate
    (θ θ' : ℝ → ℝ) (hderiv : ∀ t, HasDerivAt θ (θ' t) t) (t : ℝ) :
    -Complex.I * (starRingEnd ℂ) (Complex.exp (Complex.I * θ t)) *
      deriv (fun s => Complex.exp (Complex.I * (θ s : ℂ))) t = (θ' t : ℂ) := by
  have h1 : HasDerivAt (fun s => Complex.exp (Complex.I * (θ s : ℂ)))
      (Complex.exp (Complex.I * θ t) * (Complex.I * (θ' t : ℂ))) t := by
    have h0 : HasDerivAt (fun s : ℝ => Complex.I * (θ s : ℂ)) (Complex.I * (θ' t : ℂ)) t := by
      simpa using (((hderiv t).ofReal_comp).const_mul Complex.I)
    exact h0.cexp
  rw [h1.deriv, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [show -Complex.I * Complex.exp (-Complex.I * (θ t : ℂ)) *
      (Complex.exp (Complex.I * (θ t : ℂ)) * (Complex.I * (θ' t : ℂ)))
      = (-Complex.I * Complex.I) * (Complex.exp (-Complex.I * (θ t : ℂ)) *
        Complex.exp (Complex.I * (θ t : ℂ))) * (θ' t : ℂ) by ring,
    ← Complex.exp_add]
  simp [Complex.I_mul_I]

/-- **Key intermediate lemma (fundamental theorem of calculus for the Berry connection).**

If the phase `θ` of a state evolves with (continuous) rate `θ'`, then the accumulated Berry
phase along the loop, `∫₀¹ θ' t dt`, equals the net change of the phase `θ 1 - θ 0`. -/
