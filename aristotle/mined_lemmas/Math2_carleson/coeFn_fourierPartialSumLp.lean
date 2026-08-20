/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import line, so the
required header is reproduced here as a plain comment and again as a module
docstring immediately after the import.)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology
open scoped ENNReal

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f` at the point `x`. -/

lemma coeFn_fourierPartialSumLp (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (N : ℕ) :
    ⇑(fourierPartialSumLp f N) =ᵐ[AddCircle.haarAddCircle] fourierPartialSum (⇑f) N := by
  have h2 : ∀ᵐ x ∂(@AddCircle.haarAddCircle T hT), ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (fourierCoeff (⇑f) n • fourierLp (T := T) 2 n) x = fourierCoeff (⇑f) n * fourier n x := by
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [Lp.coeFn_smul (fourierCoeff (⇑f) n) (fourierLp (T := T) 2 n),
      coeFn_fourierLp (T := T) 2 n] with x h1 h3
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h3]
  have hA : ⇑(fourierPartialSumLp f N) =ᵐ[AddCircle.haarAddCircle]
      fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fourierCoeff (⇑f) n • fourierLp (T := T) 2 n) x :=
    coeFn_lpSum _ _
  filter_upwards [hA, h2] with x hx hx2
  simp only [fourierPartialSum]
  rw [hx]
  exact Finset.sum_congr rfl hx2

/-- The symmetric partial sums of the Fourier series of an `L²` function converge to it
in measure (along the full sequence of cut-offs). -/
