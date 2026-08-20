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

noncomputable def equiSubmodule (x : ℕ → AddCircle T) : Submodule ℂ C(AddCircle T, ℂ) where
  carrier := {f : C(AddCircle T, ℂ) |
    Tendsto (weylAvg x (⇑f)) atTop (𝓝 (∫ t : AddCircle T, f t ∂haarAddCircle))}
  zero_mem' := by
    have h0 : weylAvg x (⇑(0 : C(AddCircle T, ℂ))) = fun _ => (0 : ℂ) := by
      funext N; simp [weylAvg]
    have hz : (∫ t : AddCircle T, (0 : C(AddCircle T, ℂ)) t ∂haarAddCircle) = 0 := by simp
    show Tendsto (weylAvg x ⇑(0 : C(AddCircle T, ℂ))) atTop (𝓝 _)
    rw [h0, hz]
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    have hint : ∫ t : AddCircle T, (f + g) t ∂haarAddCircle
        = (∫ t : AddCircle T, f t ∂haarAddCircle) + ∫ t : AddCircle T, g t ∂haarAddCircle := by
      simpa using integral_add (integrable_contMap f) (integrable_contMap g)
    rw [hint]
    have hfun : weylAvg x (⇑(f + g)) = fun N => weylAvg x (⇑f) N + weylAvg x (⇑g) N := by
      funext N; simpa using weylAvg_add x (⇑f) (⇑g) N
    rw [hfun]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    have hint : ∫ t : AddCircle T, (c • f) t ∂haarAddCircle
        = c * ∫ t : AddCircle T, f t ∂haarAddCircle := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      simpa using integral_smul c (fun t : AddCircle T => f t) (μ := haarAddCircle)
    rw [hint]
    have hfun : weylAvg x (⇑(c • f)) = fun N => c * weylAvg x (⇑f) N := by
      funext N; simpa using weylAvg_smul x c (⇑f) N
    rw [hfun]
    exact hf.const_mul c

