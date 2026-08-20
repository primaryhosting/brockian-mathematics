import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

theorem hydrogen_energy_lower_bound (hardy : HardyInequality) {Z : ℝ} (hZ : 0 < Z)
    (u : Space 3 → ℝ) (hu : Differentiable ℝ u)
    (hu2 : Integrable (fun x => (u x) ^ 2))
    (hg : Integrable (fun x => ‖gradient u x‖ ^ 2))
    (hh : Integrable (fun x => (u x) ^ 2 / ‖x‖ ^ 2))
    (hc : Integrable (fun x => (u x) ^ 2 / ‖x‖))
    (hnorm : (∫ x, (u x) ^ 2) = 1) :
    -Z ^ 2 ≤ (∫ x, ‖gradient u x‖ ^ 2) - Z * ∫ x, (u x) ^ 2 / ‖x‖ := by
  set T := ∫ x, ‖gradient u x‖ ^ 2 with hT
  set H := ∫ x, (u x) ^ 2 / ‖x‖ ^ 2 with hH
  set P := ∫ x, (u x) ^ 2 / ‖x‖ with hP
  have hRint : Integrable (fun x : Space 3 => (4*Z)⁻¹ * ((u x)^2/‖x‖^2) + Z*(u x)^2) :=
    (hh.const_mul _).add (hu2.const_mul _)
  have hpt : ∀ x : Space 3, (u x)^2/‖x‖ ≤ (4*Z)⁻¹ * ((u x)^2/‖x‖^2) + Z*(u x)^2 :=
    fun x => coulomb_le_of_hardy_pointwise hZ (norm_nonneg x) (u x)
  have hbound : P ≤ (4*Z)⁻¹ * H + Z * 1 := by
    have hm := integral_mono hc hRint hpt
    rwa [integral_add (hh.const_mul _) (hu2.const_mul _), integral_const_mul,
      integral_const_mul, hnorm] at hm
  have hHT : H ≤ 4 * T := hardy u hu hu2 hg hh
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  have hstep : P ≤ T/Z + Z := by
    have h1 : (4*Z)⁻¹ * H ≤ (4*Z)⁻¹ * (4*T) :=
      mul_le_mul_of_nonneg_left hHT (by positivity)
    have h2 : (4*Z)⁻¹ * (4*T) = T/Z := by field_simp
    linarith
  have h2 : Z * P ≤ Z * (T/Z + Z) := mul_le_mul_of_nonneg_left hstep hZ.le
  have h3 : Z * (T/Z + Z) = T + Z^2 := by field_simp
  linarith

/-- **Lieb–Thirring and stability of matter.**

1. The Lieb–Thirring bound on sums of negative eigenvalues of `-Δ + V` on `L²(ℝ^d)`
   reduces, by Legendre duality, to the kinetic-energy form of the Lieb–Thirring
   inequality with the explicit positive constant `ltConst d L`.
2. Base case of stability of matter: a system of `N` electrons and `K` nuclei carrying no
   charge has nonnegative energy, so it obeys the stability bound `E ≥ -C (N + K)`.
3. Base case of stability of matter: given Hardy's inequality, a hydrogenic atom of nuclear
   charge `Z > 0` has energy at least `-Z²`. -/
