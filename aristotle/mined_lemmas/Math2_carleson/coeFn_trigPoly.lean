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

theorem coeFn_trigPoly (c : ℤ → ℂ) (s : Finset ℤ) :
    ⇑(∑ i ∈ s, c i • (fourierLp (T := (1 : ℝ)) 2 i)) =ᵐ[haarAddCircle]
      fun x => ∑ i ∈ s, c i * fourier i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 (haarAddCircle (T := (1 : ℝ)))
  | insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (c a • (fourierLp (T := (1 : ℝ)) 2 a))
          (∑ i ∈ s, c i • fourierLp 2 i),
        Lp.coeFn_smul (c a) (fourierLp (T := (1 : ℝ)) 2 a), coeFn_fourierLp (T := (1 : ℝ)) 2 a, ih]
        with x hx hsm hfl hx2
      rw [Finset.sum_insert ha, hx, Pi.add_apply, hsm, hx2, Finset.sum_insert ha, Pi.smul_apply,
        hfl, smul_eq_mul]

/-- The `L²` approximation property: the partial Fourier sums eventually approximate an `L²`
function to within any prescribed accuracy in the `L²` norm.  (This is the classical
Riesz–Fischer statement, which does *not* need Carleson's theorem.) -/
