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

theorem harmonic_oscillator_virial :
    2 * (∫ x : ℝ, (1 / 2) * (hoDPsi x) ^ 2) = ∫ x : ℝ, x * hoDV x * (hoPsi x) ^ 2 ∧
      (∫ x : ℝ, ((1 / 2) * (hoDPsi x) ^ 2 + hoV x * (hoPsi x) ^ 2)) = 1 / 2 := by
  refine virial_theorem hoPsi hoDPsi hoDDPsi hoV hoDV (1 / 2)
    hasDerivAt_hoPsi hasDerivAt_hoDPsi hasDerivAt_hoV ho_schrodinger ho_norm
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2) 0 ?_)
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2 / 2) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (-(hoC ^ 2)) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (-(hoC ^ 2) / 2) 4 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (hoC ^ 2) 1 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (hoC ^ 2) 1 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (hoC ^ 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (hoC ^ 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (hoC ^ 2 / 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (hoC ^ 2 / 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (-(hoC ^ 2)) 1 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (-(hoC ^ 2)) 1 ?_) <;>
  · intro x
    have hE : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]
      ring_nf
    simp only [hoPsi, hoDPsi, hoV, hoDV, hE]
    ring

end Phys

/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open MeasureTheory Filter Topology

/-- Fundamental theorem of calculus on the whole line, in the form used for
integrating by parts against a decaying boundary term: if `f` is everywhere
differentiable with integrable derivative `f'` and `f → 0` at both ends of the
line, then `∫ f' = 0`. -/
