import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle T → ℂ`,
i.e. `∑_{|n| ≤ N} (fourierCoeff f n) * e^{2πinx/T}`. -/

lemma coeFn_fourier_sum (f : Lp ℂ 2 (@haarAddCircle T hT)) (s : Finset ℤ) :
    ⇑(∑ i ∈ s, fourierCoeff (⇑f) i • fourierLp 2 i)
      =ᵐ[@haarAddCircle T hT] fun x => ∑ i ∈ s, fourierCoeff (⇑f) i * fourier i x := by
  classical
  have h1 := coeFn_finset_sum_Lp (T := T) s
    (fun i => fourierCoeff (⇑f) i • (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT)))
  have h2 : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ i ∈ s,
      (fourierCoeff (⇑f) i • (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT))) x
        = fourierCoeff (⇑f) i * fourier i x := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [Lp.coeFn_smul (fourierCoeff (⇑f) i)
        (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT)),
      coeFn_fourierLp (T := T) 2 i] with x hx hx'
    rw [hx]
    simp only [Pi.smul_apply, hx', smul_eq_mul]
  filter_upwards [h1, h2] with x hx hx'
  rw [hx]
  exact Finset.sum_congr rfl fun i hi => hx' i hi

/-- The sets `Finset.Icc (-N) N`, `N : ℕ`, are monotone and exhaust `ℤ`, hence tend to `atTop`
in the filter of finite subsets of `ℤ`. -/
