/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma empirical_real_inter_Icc (θ : ℕ → ℝ) (hmem : ∀ p, θ p ∈ Icc 0 Real.pi) (X : ℕ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (empirical θ X).real s = (empirical θ X).real (s ∩ Icc 0 Real.pi) := by
  by_cases hX : (Nat.primesBelow X).card = 0
  · rw [empirical, if_pos hX]
    simp only [measureReal_def, Measure.dirac_apply' _ hs,
      Measure.dirac_apply' _ (hs.inter measurableSet_Icc)]
    have h0 : (0:ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, Real.pi_nonneg⟩
    by_cases h0s : (0:ℝ) ∈ s
    · simp [h0s, h0]
    · simp [h0s]

  · have hfil : ((Nat.primesBelow X).filter fun p => θ p ∈ s)
        = ((Nat.primesBelow X).filter fun p => θ p ∈ s ∩ Icc 0 Real.pi) :=
      Finset.filter_congr fun p _ => by simp only [Set.mem_inter_iff, and_iff_left (hmem p)]
    rw [empirical_real θ hX hs, empirical_real θ hX (hs.inter measurableSet_Icc), hfil]
    congr!

/-- Any open interval, intersected with `[0, π]`, is squeezed between a closed subinterval
`[α, β]` of `[0, π]` and that subinterval together with its two endpoints. -/
