import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = ContinuousLinearMap.id ℂ H
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  inner_map : ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  cont : ∀ x, Continuous fun t => U t x

variable {U : ℝ → H →L[ℂ] H}

/-- The natural domain of the generator: those vectors for which `t ↦ U t x` is
differentiable at `0`. -/

theorem integral_mem_domain (hU : IsUnitaryGroup U) (x : H) (r : ℝ) :
    (∫ s in (0:ℝ)..r, U s x) ∈ domain U := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => U s x) MeasureTheory.volume a b :=
    fun a b => (hU.cont x).intervalIntegrable a b
  have key : ∀ t : ℝ, U t (∫ s in (0:ℝ)..r, U s x)
      = (∫ s in (0:ℝ)..(t + r), U s x) - (∫ s in (0:ℝ)..t, U s x) := by
    intro t
    have h1 : U t (∫ s in (0:ℝ)..r, U s x) = ∫ s in (0:ℝ)..r, U t (U s x) :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (U t) (hint 0 r)).symm
    have h2 : ∀ s : ℝ, U t (U s x) = U (t + s) x := by
      intro s; rw [← ContinuousLinearMap.comp_apply, ← hU.map_add]
    rw [h1]
    simp_rw [h2]
    rw [intervalIntegral.integral_comp_add_left (fun u : ℝ => U u x) t, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hint 0 (t + r)) (hint 0 t)).symm
  refine ⟨U r x - x, ?_⟩
  have hd : HasDerivAt
      (fun t : ℝ => (∫ s in (0:ℝ)..(t + r), U s x) - (∫ s in (0:ℝ)..t, U s x))
      (U (0 + r) x - U 0 x) 0 :=
    (HasDerivAt.comp_add_const (f := fun u : ℝ => ∫ s in (0:ℝ)..u, U s x) 0 r
      (hasDerivAt_integral hU x (0 + r))).sub (hasDerivAt_integral hU x 0)
  simp only [zero_add, hU.map_zero, ContinuousLinearMap.id_apply] at hd
  simpa only [key] using hd

