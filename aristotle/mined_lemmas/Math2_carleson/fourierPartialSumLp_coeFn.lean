/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The symmetric partial sum of the Fourier series of `f` at `x`:
`∑_{n = -N}^{N} (fourierCoeff f n) e^{2πinx/T}`. -/

lemma fourierPartialSumLp_coeFn (f : Lp ℂ 2 (@haarAddCircle T hT)) (N : ℕ) :
    (fourierPartialSumLp f N : AddCircle T → ℂ)
      =ᵐ[(@haarAddCircle T hT)] fourierPartialSum (f : AddCircle T → ℂ) N := by
  have h1 := coeFn_finset_sum_Lp (μ := (@haarAddCircle T hT))
    (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourierLp 2 n)
  have h2 : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ n : ℤ,
      ((fourierCoeff (f : AddCircle T → ℂ) n • fourierLp (T := T) 2 n : Lp ℂ 2 _) :
          AddCircle T → ℂ) x
        = fourierCoeff (f : AddCircle T → ℂ) n • fourier n x := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (fourierCoeff (f : AddCircle T → ℂ) n)
      (fourierLp (T := T) 2 n), coeFn_fourierLp (T := T) 2 n] with x hx hx'
    rw [hx, Pi.smul_apply, hx']
  filter_upwards [h1, h2] with x hx hx2
  simp only [fourierPartialSum, fourierPartialSumLp]
  rw [hx]
  exact Finset.sum_congr rfl fun n _ => hx2 n

/-- Auxiliary version of convergence in measure, phrased with the `L²` partial sums. -/
