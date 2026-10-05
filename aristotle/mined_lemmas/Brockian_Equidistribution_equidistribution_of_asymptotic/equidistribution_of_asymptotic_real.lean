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

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open Filter MeasureTheory AddCircle

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Cesàro average of `f` along the first `N` terms of the sequence `u`. -/

theorem equidistribution_of_asymptotic_real (u : ℕ → AddCircle T)
    (hu : ∀ m : ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (u n)) atTop (nhds 0))
    (f : C(AddCircle T, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (u n)) atTop
      (nhds (∫ x, f x ∂(@haarAddCircle T hT))) := by
  set F : C(AddCircle T, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    with hF
  have hmain := equidistribution_of_asymptotic u hu F
  have hint : ∫ x, F x ∂(@haarAddCircle T hT) = ((∫ x, f x ∂(@haarAddCircle T hT) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hcast : ∀ N : ℕ, (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, F (u n)
      = (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (u n) : ℝ) : ℂ) := by
    intro N
    push_cast [hF]
    rfl
  rw [hint] at hmain
  simp only [hcast] at hmain
  exact tendsto_ofReal_iff.mp hmain

end Brockian.Equidistribution

