/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set

namespace Phys

section Kato

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Differentiating the idempotency relation `P s * P s = P s`. -/

theorem adiabatic_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ham P dP U : ℝ → (E →L[ℂ] E)) (eig : ℝ → ℂ) (ε : ℝ) (psi : E)
    (hHam : Continuous Ham)
    (hP : ∀ s, HasDerivAt P (dP s) s) (hdP : Continuous dP)
    (hproj : ∀ s, P s * P s = P s)
    (heig : ∀ s, Ham s * P s = eig s • P s)
    (heig' : ∀ s, P s * Ham s = eig s • P s)
    (hnondeg : ∀ s, ∃ w : E, w ≠ 0 ∧ ∀ x : E, ∃ c : ℂ, P s x = c • w)
    (hU : ∀ s, HasDerivAt U
      (((-(Complex.I / ε)) • Ham s + (dP s * P s - P s * dP s)) * U s) s)
    (hU0 : U 0 = 1)
    (hpsi : P 0 psi = psi)
    {s : ℝ} (hs : 0 ≤ s) :
    P s (U s psi) = U s psi ∧ Ham s (U s psi) = eig s • (U s psi) := by
  set C : ℝ → (E →L[ℂ] E) := fun t => (-(Complex.I / ε)) • Ham t with hC
  have hCcont : Continuous C := hHam.const_smul _
  have hcomm : ∀ t, C t * P t = P t * C t := by
    intro t
    simp only [hC, smul_mul_assoc, mul_smul_comm, heig t, heig' t]
  have hint : P s * U s = U s * P 0 :=
    kato_intertwining hP hdP hproj hCcont hcomm hU hU0 hs
  have h1 : P s (U s psi) = U s psi := by
    have := congrArg (fun T : E →L[ℂ] E => T psi) hint
    simpa [ContinuousLinearMap.mul_apply, hpsi] using this
  refine ⟨h1, ?_⟩
  have h2 := congrArg (fun T : E →L[ℂ] E => T (U s psi)) (heig s)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, h1] at h2
  exact h2

/-- A consistency check showing that the hypotheses of `adiabatic_theorem` are satisfiable,
so the theorem is not vacuous: on `E = ℂ`, with the constant Hamiltonian `a`, the rank-one
projection `1`, and the propagator `U s = exp (-(i/ε) a s)`, all hypotheses hold and the
conclusion applies to any initial state. -/
