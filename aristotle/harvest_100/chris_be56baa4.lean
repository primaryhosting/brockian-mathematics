import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The Berry curvature `F = ∂_{k₁} A₂ - ∂_{k₂} A₁` of a `U(1)` Berry connection
`(A₁, A₂)` on the Brillouin torus, written in coordinates. -/
noncomputable def berryCurvature (A₁ A₂ : ℝ → ℝ → ℝ) (k₁ k₂ : ℝ) : ℝ :=
  deriv (fun x : ℝ => A₂ x k₂) k₁ - deriv (fun y : ℝ => A₁ k₁ y) k₂

/-- The (first) Chern number of the Berry connection `(A₁, A₂)`: the integral of the
Berry curvature over the Brillouin torus `[0, 2π] × [0, 2π]`, normalized by `2π`. -/
noncomputable def chernNumber (A₁ A₂ : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ k₁ in (0:ℝ)..(2 * Real.pi), ∫ k₂ in (0:ℝ)..(2 * Real.pi), berryCurvature A₁ A₂ k₁ k₂

/-- The TKNN (Kubo) expression for the zero-temperature Hall conductance of a filled band
with Berry connection `(A₁, A₂)`, in terms of the elementary charge `e` and Planck's
constant `hP`. -/
noncomputable def hallConductance (e hP : ℝ) (A₁ A₂ : ℝ → ℝ → ℝ) : ℝ :=
  (e ^ 2 / hP) * (1 / (2 * Real.pi)) *
    ∫ k₁ in (0:ℝ)..(2 * Real.pi), ∫ k₂ in (0:ℝ)..(2 * Real.pi), berryCurvature A₁ A₂ k₁ k₂

/-- Landau-gauge Berry connection of a band with Chern number `n`: first component. -/
def landauA₁ (_n : ℤ) : ℝ → ℝ → ℝ := fun _ _ => 0

/-- Landau-gauge Berry connection of a band with Chern number `n`: second component. -/
noncomputable def landauA₂ (n : ℤ) : ℝ → ℝ → ℝ := fun k₁ _ => (n : ℝ) * k₁ / (2 * Real.pi)

/-- The Berry curvature of the Landau-gauge connection is the constant `n / (2π)`. -/
lemma berryCurvature_landau (n : ℤ) (k₁ k₂ : ℝ) :
    berryCurvature (landauA₁ n) (landauA₂ n) k₁ k₂ = (n : ℝ) / (2 * Real.pi) := by
  have h1 : deriv (fun x : ℝ => landauA₂ n x k₂) k₁ = (n : ℝ) / (2 * Real.pi) := by
    simp only [landauA₂]
    rw [show (fun x : ℝ => (n : ℝ) * x / (2 * Real.pi))
        = fun x : ℝ => ((n : ℝ) / (2 * Real.pi)) * x by funext x; ring]
    have hd : HasDerivAt (fun x : ℝ => ((n : ℝ) / (2 * Real.pi)) * x)
        ((n : ℝ) / (2 * Real.pi)) k₁ := by
      simpa using (hasDerivAt_id k₁).const_mul ((n : ℝ) / (2 * Real.pi))
    exact hd.deriv
  have h2 : deriv (fun y : ℝ => landauA₁ n k₁ y) k₂ = 0 := by
    simp [landauA₁]
  simp [berryCurvature, h1, h2]

/-- **Key intermediate lemma (quantization).** The integral of the Berry curvature over the
Brillouin torus is `2π n`; equivalently the Chern number of the model is the integer `n`. -/
lemma chernNumber_landau (n : ℤ) : chernNumber (landauA₁ n) (landauA₂ n) = (n : ℝ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hinner : ∀ k₁ : ℝ,
      (∫ k₂ in (0:ℝ)..(2 * Real.pi), berryCurvature (landauA₁ n) (landauA₂ n) k₁ k₂)
        = (n : ℝ) := by
    intro k₁
    simp only [berryCurvature_landau]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  simp only [chernNumber, hinner]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- **TKNN.** For the Landau-gauge band with Berry connection `(landauA₁ n, landauA₂ n)`,
the Hall conductance equals the Chern number times `e² / h`, and that Chern number is the
integer `n`; hence the Hall conductance is quantized in units of `e² / h`. -/
theorem tknn_chern_hall (e hP : ℝ) (n : ℤ) :
    hallConductance e hP (landauA₁ n) (landauA₂ n)
        = chernNumber (landauA₁ n) (landauA₂ n) * (e ^ 2 / hP) ∧
      chernNumber (landauA₁ n) (landauA₂ n) = (n : ℝ) ∧
      hallConductance e hP (landauA₁ n) (landauA₂ n) = (n : ℝ) * (e ^ 2 / hP) := by
  have hC : chernNumber (landauA₁ n) (landauA₂ n) = (n : ℝ) := chernNumber_landau n
  have hEq : hallConductance e hP (landauA₁ n) (landauA₂ n)
      = chernNumber (landauA₁ n) (landauA₂ n) * (e ^ 2 / hP) := by
    simp only [hallConductance, chernNumber]
    ring
  exact ⟨hEq, hC, by rw [hEq, hC]⟩

end Frontier

