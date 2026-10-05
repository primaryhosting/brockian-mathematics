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

import Mathlib
/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module doc comment, so the
-- header block above appears immediately after the single required import.)

open scoped BigOperators
open scoped Real

namespace Brockian

open Matrix

/-! ## The trace norm of a Hermitian matrix -/

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

lemma hermTraceNorm_of_cube {A : Matrix n n ℂ} (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    (hcube : A * A * A = ((s ^ 2 : ℝ) : ℂ) • A)
    (htr : (A * A).trace = ((2 * s ^ 2 : ℝ) : ℂ)) :
    hermTraceNorm hA = 2 * s := by
  have key : ∀ i, (hA.eigenvalues i) ^ 2 = s * |hA.eigenvalues i| := by
    intro i
    have h := eigenvalues_cube hA hcube i
    set l := hA.eigenvalues i with hlv
    rcases eq_or_ne l 0 with h0 | h0
    · simp [h0]
    · have hsq : l ^ 2 = s ^ 2 := by field_simp at h; linarith [h]
      have habs : |l| = s := by
        have habs' : |l| = |s| := by rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hsq]
        rwa [abs_of_nonneg hs] at habs'
      rw [habs, hsq]; ring
  have hsum : ∑ i, (hA.eigenvalues i) ^ 2 = 2 * s ^ 2 := sum_sq_eigenvalues_eq hA htr
  have hmain : s * hermTraceNorm hA = 2 * s ^ 2 := by
    rw [hermTraceNorm, Finset.mul_sum, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (key i).symm
  rcases eq_or_lt_of_le hs with h0 | h0
  · have hz : ∀ i, hA.eigenvalues i = 0 := by
      intro i
      have hk := key i
      rw [← h0] at hk
      exact pow_eq_zero_iff two_ne_zero |>.mp (by simpa using hk)
    simp [hermTraceNorm, hz, ← h0]
  · nlinarith [hmain, h0]

end Spectral

/-! ## The trace distance between two pure states -/

section Main

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For unit vectors `u`, `v` the overlap `‖⟪u,v⟫‖` is at most `1`.  (Proved here from the
trace identity `tr((P-Q)²) = 2(1 - ‖⟪u,v⟫‖²) = ∑ λᵢ² ≥ 0`.) -/
