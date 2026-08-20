/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

namespace Brockian

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
indexed by `k : ZMod n`. -/

theorem PentagonPentagonEquivarianceGeneral (n : ℕ) (hn : 0 < n) :
    (∀ k : ZMod n, ngonIndexAction n 1 k = k) ∧
    (∀ g h : DihedralGroup n, ∀ k : ZMod n,
        ngonIndexAction n (g * h) k = ngonIndexAction n g (ngonIndexAction n h k)) ∧
    (∀ z : ℂ, ngonPlaneAction n 1 z = z) ∧
    (∀ g h : DihedralGroup n, ∀ z : ℂ,
        ngonPlaneAction n (g * h) z = ngonPlaneAction n g (ngonPlaneAction n h z)) ∧
    (∀ g : DihedralGroup n, ∀ k : ZMod n,
        ngonPlaneAction n g (ngonVertex n k) = ngonVertex n (ngonIndexAction n g k)) ∧
    (∀ k : ZMod n, ‖ngonVertex n k‖ = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [DihedralGroup.one_def]
    simp [ngonIndexAction]
  · rintro (i | i) (j | j) k <;>
      simp [ngonIndexAction, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring
  · intro z
    rw [DihedralGroup.one_def]
    simp [ngonPlaneAction]
  · rintro (i | i) (j | j) z
    · simp only [DihedralGroup.r_mul_r, ngonPlaneAction, neg_add]
      rw [ngonVertex_add hn]
      ring
    · simp only [DihedralGroup.r_mul_sr, ngonPlaneAction]
      rw [show j - i = j + -i by ring, ngonVertex_add hn]
      ring
    · simp only [DihedralGroup.sr_mul_r, ngonPlaneAction]
      rw [ngonVertex_add hn, ngonVertex_neg hn, map_mul, Complex.conj_conj]
      ring
    · simp only [DihedralGroup.sr_mul_sr, ngonPlaneAction]
      rw [show -(j - i) = i + -j by ring, ngonVertex_add hn, ngonVertex_neg hn, map_mul,
        Complex.conj_conj]
      ring
  · rintro (i | i) k
    · simp only [ngonPlaneAction, ngonIndexAction]
      rw [show k - i = -i + k by ring, ngonVertex_add hn]
    · simp only [ngonPlaneAction, ngonIndexAction]
      rw [ngonVertex_sub hn]
  · intro k
    exact norm_ngonVertex n k

/-- The original pentagon (`D₅`) case, obtained from the general theorem. -/
