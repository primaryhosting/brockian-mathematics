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

theorem exists_subseq_ae_tendsto_partialFourierSum (hf : MemLp f 2 haarAddCircle) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂haarAddCircle, Tendsto (fun i => partialFourierSum f (ns i) x) atTop (𝓝 (f x)) := by
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable (partialFourierSum f N) haarAddCircle := fun N =>
    (continuous_partialFourierSum f N).aestronglyMeasurable
  have htend : Tendsto (fun N : ℕ => eLpNorm (partialFourierSum f N - f) 2 haarAddCircle)
      atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_partialFourierSum hf
    refine h.congr fun N => ?_
    rw [← eLpNorm_neg]
    congr 1
    funext x
    simp
  exact (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hmeas
    hf.aestronglyMeasurable htend).exists_seq_tendsto_ae

end Basic

/-- Pointwise, each partial sum is dominated by the Carleson maximal operator. -/
