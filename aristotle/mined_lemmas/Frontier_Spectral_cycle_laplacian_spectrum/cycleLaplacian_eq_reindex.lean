/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma cycleLaplacian_eq_reindex :
    cycleLaplacian n
      = Matrix.reindex (finZModEquiv n).symm (finZModEquiv n).symm (cycleLaplacianZ n) := by
  ext i j
  have hi : ((i.val : ZMod n)).val = i.val := ZMod.val_natCast_of_lt i.isLt
  have hj : ((j.val : ZMod n)).val = j.val := ZMod.val_natCast_of_lt j.isLt
  have heq : ((i.val : ZMod n) = (j.val : ZMod n)) ↔ i = j := by
    constructor
    · intro h
      have := congrArg ZMod.val h
      rw [hi, hj] at this
      exact Fin.ext this
    · rintro rfl; rfl
  have h1 : (i.val + 1) % n = j.val ↔ (i.val : ZMod n) - (j.val : ZMod n) = -1 := by
    have h := succ_val_iff ((i.val : ZMod n)) ((j.val : ZMod n))
    rw [hi, hj, add_one_iff_sub_eq_neg_one] at h
    exact h
  have h2 : (j.val + 1) % n = i.val ↔ (i.val : ZMod n) - (j.val : ZMod n) = 1 := by
    have h := succ_val_iff ((j.val : ZMod n)) ((i.val : ZMod n))
    rw [hi, hj, add_one_iff_sub_eq_neg_one] at h
    rw [h]
    constructor
    · intro hh; linear_combination -hh
    · intro hh; linear_combination -hh
  simp only [cycleLaplacian, cycleLaplacianZ, Matrix.of_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, finZModEquiv, Equiv.coe_fn_mk]
  by_cases hij : i = j
  · subst hij; simp
  · have hij' : ((i.val : ZMod n)) ≠ (j.val : ZMod n) := fun h => hij (heq.mp h)
    rw [if_neg hij, if_neg hij']
    by_cases hc : (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
    · rw [if_pos hc, if_pos]
      rcases hc with h | h
      · exact Or.inr (h1.mp h)
      · exact Or.inl (h2.mp h)
    · rw [if_neg hc, if_neg]
      rintro (h | h)
      · exact hc (Or.inr (h2.mpr h))
      · exact hc (Or.inl (h1.mpr h))

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian of
the cycle `C n` are exactly `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`. -/
