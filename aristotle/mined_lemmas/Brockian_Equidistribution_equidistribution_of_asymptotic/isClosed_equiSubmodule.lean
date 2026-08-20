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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology Submodule Set
open AddCircle (haarAddCircle)

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th Weyl average of `f` along the sequence `x`, i.e.
`(1/N) * ∑_{n < N} f (x n)` (equal to `0` when `N = 0`). -/

lemma isClosed_equiSubmodule (x : ℕ → AddCircle T) :
    IsClosed ((equiSubmodule x : Submodule ℂ C(AddCircle T, ℂ)) : Set C(AddCircle T, ℂ)) := by
  apply isClosed_of_closure_subset
  intro f hf
  rw [SetLike.mem_coe, mem_equiSubmodule_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by linarith)
  rw [SetLike.mem_coe, mem_equiSubmodule_iff, Metric.tendsto_atTop] at hgS
  obtain ⟨N₀, hN₀⟩ := hgS (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖weylAvg x (⇑f) N - weylAvg x (⇑g) N‖ ≤ ‖f - g‖ := by
    have he : weylAvg x (⇑f) N - weylAvg x (⇑g) N = weylAvg x (⇑(f - g)) N := by
      simpa using (weylAvg_sub x (⇑f) (⇑g) N).symm
    rw [he]
    exact norm_weylAvg_le x (f - g) N
  have h3 : ‖(∫ t : AddCircle T, g t ∂haarAddCircle) - ∫ t : AddCircle T, f t ∂haarAddCircle‖
      ≤ ‖g - f‖ := by
    have hint : (∫ t : AddCircle T, g t ∂haarAddCircle)
        - (∫ t : AddCircle T, f t ∂haarAddCircle)
        = ∫ t : AddCircle T, (g - f) t ∂haarAddCircle := by
      simpa using (integral_sub (integrable_contMap g) (integrable_contMap f)).symm
    rw [hint]
    exact norm_integral_le_norm (g - f)
  have hnfg : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hngf : ‖g - f‖ < ε / 3 := by
    rw [← dist_eq_norm, dist_comm]; exact hfg
  have h2 : dist (weylAvg x (⇑g) N) (∫ t : AddCircle T, g t ∂haarAddCircle) < ε / 3 := hN₀ N hN
  rw [dist_eq_norm] at h2 ⊢
  calc ‖weylAvg x (⇑f) N - ∫ t : AddCircle T, f t ∂haarAddCircle‖
      = ‖(weylAvg x (⇑f) N - weylAvg x (⇑g) N)
          + (weylAvg x (⇑g) N - ∫ t : AddCircle T, g t ∂haarAddCircle)
          + ((∫ t : AddCircle T, g t ∂haarAddCircle)
              - ∫ t : AddCircle T, f t ∂haarAddCircle)‖ := by ring_nf
    _ ≤ ‖(weylAvg x (⇑f) N - weylAvg x (⇑g) N)
          + (weylAvg x (⇑g) N - ∫ t : AddCircle T, g t ∂haarAddCircle)‖
          + ‖(∫ t : AddCircle T, g t ∂haarAddCircle)
              - ∫ t : AddCircle T, f t ∂haarAddCircle‖ := norm_add_le _ _
    _ ≤ ‖weylAvg x (⇑f) N - weylAvg x (⇑g) N‖
          + ‖weylAvg x (⇑g) N - ∫ t : AddCircle T, g t ∂haarAddCircle‖
          + ‖(∫ t : AddCircle T, g t ∂haarAddCircle)
              - ∫ t : AddCircle T, f t ∂haarAddCircle‖ := by
          gcongr
          exact norm_add_le _ _
    _ < ε := by
          have hA := h1.trans_lt hnfg
          have hB := h3.trans_lt hngf
          linarith

/-- The mean value of a nonzero Fourier character vanishes. -/
