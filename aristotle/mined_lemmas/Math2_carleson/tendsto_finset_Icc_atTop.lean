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

lemma tendsto_finset_Icc_atTop :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro M N hMN i hi
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨le_trans (neg_le_neg (by exact_mod_cast hMN)) hi.1,
      le_trans hi.2 (by exact_mod_cast hMN)⟩
  · intro i
    refine ⟨i.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega

/-- **Key intermediate step**: the symmetric partial sums of the Fourier series of an `L²`
function converge to it in the `L²` norm. -/
