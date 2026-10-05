/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

theorem donsker_invariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion P' B)
    {u : ℕ → ℝ} (hu : Monotone u) (hu0 : u 0 = 0) (k : ℕ)
    (f : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω) ∂P) atTop
      (𝓝 (∫ ω, f (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω) ∂P')) := by
  have hu0' : (0 : ℝ) ≤ u 0 := le_of_eq hu0.symm
  set g : BoundedContinuousFunction (Fin k → ℝ) ℝ :=
    f.compContinuous ⟨cumSumCLM k, (cumSumCLM k).continuous⟩ with hg
  have hgapp : ∀ y : Fin k → ℝ, g y = f (cumSumCLM k y) := fun y ↦ rfl
  -- the walk side
  have hleft : ∀ n : ℕ, ∫ ω, f (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω) ∂P
      = ∫ x, g x ∂(Measure.pi fun j : Fin k ↦ gaussianReal 0 (walkIncrVar u n (j : ℕ))) := by
    intro n
    have hpt : ∀ ω, f (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω)
        = g fun j : Fin k ↦ walkIncr X u n (j : ℕ) ω := by
      intro ω
      rw [hgapp, ← donskerStep_eq_cumSum hu hu0 n k ω]
    simp_rw [hpt]
    rw [← map_walkIncr_vector hmeas hindep hlaw hu n k,
      integral_map (measurable_pi_lambda _ fun j ↦ measurable_walkIncr hmeas u n (j : ℕ)).aemeasurable
        g.continuous.aestronglyMeasurable]
  -- the Brownian side
  have hright : ∫ ω, f (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω) ∂P'
      = ∫ x, g x ∂(Measure.pi fun j : Fin k ↦
          gaussianReal 0 (u ((j : ℕ) + 1) - u (j : ℕ)).toNNReal) := by
    have hpt : ∀ ω, f (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω)
        = g fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω - B (u (j : ℕ)) ω := by
      intro ω
      rw [hgapp, ← bm_eq_cumSum hB.start_zero hu0 k ω]
    simp_rw [hpt]
    rw [← map_bmIncr_vector hB hu hu0' k,
      integral_map (measurable_pi_lambda _ fun j ↦
        ((hB.measurable _).sub (hB.measurable _))).aemeasurable
        g.continuous.aestronglyMeasurable]
  simp_rw [hleft, hright]
  refine tendsto_integral_pi_gaussian (fun j ↦ ?_) g
  rw [Real.coe_toNNReal _ (sub_nonneg.2 (hu (Nat.le_succ _)))]
  exact tendsto_walkIncrVar hu hu0' (j : ℕ)

end Math2

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

