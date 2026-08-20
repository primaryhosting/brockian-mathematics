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

theorem fourierCoeff_partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (m : ℤ) :
    fourierCoeff (partialFourierSum f N) m =
      if m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then fourierCoeff f m else 0 := by
  have h : partialFourierSum f N
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (fun x => fourierCoeff f n * fourier n x) := by
    funext x; simp [partialFourierSum]
  rw [h, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun n _ => by
      rw [fourierCoeff.const_mul (fun x => fourier n x) (fourierCoeff f n) m,
        show (fun x => (fourier n) x) = ⇑(fourier (T := (1 : ℝ)) n) from rfl,
        fourierCoeff_fourier n])]
    simp [Pi.single_apply, mul_ite]
  · intro n _
    exact ((map_continuous (fourier n)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl |>.const_mul _

/-- Partial sums reproduce trigonometric polynomials: the `M`-th partial sum of the `N`-th
partial sum of `f` is the `N`-th partial sum of `f`, provided `N ≤ M`. -/
