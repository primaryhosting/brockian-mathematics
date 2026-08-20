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

theorem adiabatic_theorem_example (a : ℂ) (eps : ℝ) (psi : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    (1 : ℂ →L[ℂ] ℂ) ((Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi)
        = (Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi ∧
      (a • (1 : ℂ →L[ℂ] ℂ)) ((Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi)
        = a • ((Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi) := by
  refine adiabatic_theorem (fun _ => a • (1 : ℂ →L[ℂ] ℂ)) (fun _ => (1 : ℂ →L[ℂ] ℂ))
    (fun _ => (0 : ℂ →L[ℂ] ℂ))
    (fun t => Complex.exp (-(Complex.I / eps) * a * t) • (1 : ℂ →L[ℂ] ℂ)) (fun _ => a) eps psi
    continuous_const (fun t => hasDerivAt_const t _) continuous_const (fun _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ => ⟨1, one_ne_zero, fun x => ⟨x, by simp⟩⟩)
    ?_ (by simp) (by simp) hs
  intro t
  set z : ℂ := -(Complex.I / eps) * a with hz
  have h1 : HasDerivAt (fun r : ℝ => (z * r : ℂ)) z t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul z)
  have h2 : HasDerivAt (fun r : ℝ => Complex.exp (z * r)) (z * Complex.exp (z * t)) t := by
    simpa [mul_comm] using h1.cexp
  have h3 := h2.smul_const (1 : ℂ →L[ℂ] ℂ)
  convert h3 using 1
  simp [smul_smul, hz, mul_comm]

end Phys

