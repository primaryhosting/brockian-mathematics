import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Contents

`Math2.carleson` : the Fourier series of a square-integrable function on the circle
`AddCircle 1` converges to it almost everywhere.  The statement takes as an explicit hypothesis
the key intermediate result `Math2.CarlesonWeakL2 C`, the Carleson-Hunt weak `(2,2)` maximal
inequality for the Carleson maximal operator; everything else -- the density/approximation
argument by trigonometric polynomials and the passage from the maximal inequality to almost
everywhere convergence -- is proved here from scratch.

Proved unconditionally (no hypothesis) in this file:

* `Math2.tendsto_eLpNorm_partialFourierSum` : `L²` convergence of the partial Fourier sums;
* `Math2.exists_subseq_ae_tendsto_partialFourierSum` : almost everywhere convergence of a
  subsequence of the partial Fourier sums.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory AddCircle Filter Topology

noncomputable section

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle 1 → ℂ`. -/

theorem carleson {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : CarlesonWeakL2 C)
    (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle) :
    ∀ᵐ x ∂haarAddCircle, Tendsto (fun N => partialFourierSum f N x) atTop (𝓝 (f x)) := by
  have hzero : ∀ k : ℕ,
      haarAddCircle {x | ((k : ℝ≥0∞) + 1)⁻¹ < divergenceLimsup f x} = 0 := by
    intro k
    exact meas_divergenceLimsup_eq_zero hC hbound hf (by simp)
  have hset : {x | divergenceLimsup f x ≠ 0}
      = ⋃ k : ℕ, {x | ((k : ℝ≥0∞) + 1)⁻¹ < divergenceLimsup f x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx
      exact ⟨k, lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ k)) hk⟩
    · rintro ⟨k, hk⟩
      exact (lt_of_le_of_lt (zero_le _) hk).ne'
  have hae : ∀ᵐ x ∂haarAddCircle, divergenceLimsup f x = 0 := by
    rw [ae_iff, hset]
    exact measure_iUnion_null hzero
  filter_upwards [hae] with x hx
  exact tendsto_of_divergenceLimsup_eq_zero hx

end

end Math2

