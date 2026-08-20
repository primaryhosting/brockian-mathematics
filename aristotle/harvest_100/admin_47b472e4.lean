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
theorem berry_phase_quantized
    (θ θ' : ℝ → ℝ) (hderiv : ∀ t, HasDerivAt θ (θ' t) t) (hcont : Continuous θ')
    (hloop : Complex.exp (Complex.I * θ 0) = Complex.exp (Complex.I * θ 1)) :
    ∃ n : ℤ, ∫ t in (0:ℝ)..1, θ' t = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hloop
  refine ⟨-n, ?_⟩
  rw [berry_phase_eq_phase_difference θ θ' hderiv hcont]
  have hI : Complex.I * (((θ 0 : ℝ) : ℂ) - ((θ 1 : ℝ) : ℂ))
      = Complex.I * ((2 * Real.pi * n : ℝ) : ℂ) := by
    rw [mul_sub, hn]
    push_cast
    ring
  have hcast := mul_left_cancel₀ Complex.I_ne_zero hI
  have hreal : (θ 0 : ℝ) - θ 1 = 2 * Real.pi * n := by exact_mod_cast hcast
  push_cast
  linarith

end Frontier

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

