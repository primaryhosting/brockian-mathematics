import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset SimpleGraph Matrix

/-- The Laplacian of the cycle graph `C n` (`n ≥ 3`) acts on a vector by
`(L v) i = 2 * v i - (v (i-1) + v (i+1))`. -/

theorem cycle_rec_eigenvector {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ v : ZMod n → ℝ, v ≠ 0 ∧ (∑ i, v i = 0) ∧
      ∀ i : ZMod n, 2 * v i - (v (i - 1) + v (i + 1))
        = (2 - 2 * Real.cos (2 * Real.pi / n)) * v i := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  set psi : AddChar (ZMod n) ℂ := AddChar.circleEquivComplex (AddChar.zmod n 1) with hpsi
  have hpsi1 : psi 1 = Complex.exp (((2 * Real.pi / n : ℝ)) * Complex.I) := by
    have h := AddChar.zmod_intCast n 1 1
    simp only [Int.cast_one, one_mul] at h
    rw [hpsi, show ((AddChar.circleEquivComplex (AddChar.zmod n 1) : ZMod n → ℂ) 1)
      = ((AddChar.zmod n 1 1 : Circle) : ℂ) from rfl, h, Circle.coe_exp]
    ring_nf
  have hre : (psi 1).re = Real.cos (2 * Real.pi / n) := by
    rw [hpsi1, Complex.exp_ofReal_mul_I_re]
  have hnorm : ‖psi 1‖ = 1 := by
    rw [hpsi1]
    simp [Complex.norm_exp]
  have hz : ¬ (AddChar.zmod n (1 : ZMod n) = 0) := by
    intro h
    have h0 : AddChar.zmod n (1 : ZMod n) = AddChar.zmod n 0 := by
      rw [h, AddChar.zmod_zero]; rfl
    exact one_ne_zero (AddChar.zmod_injective h0)
  have hne0 : psi ≠ 0 := by
    rw [show psi = AddChar.zmodAddEquiv (1 : ZMod n) from rfl]
    simpa using hz
  refine ⟨fun i => (psi i).re, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · have hsum : ∑ i, (psi i).re = (∑ i, psi i).re := by
      simp [Complex.re_sum]
    rw [hsum, AddChar.sum_eq_zero_iff_ne_zero.2 hne0]
    simp
  · intro i
    have e1 : psi (i + 1) = psi i * psi 1 := by rw [AddChar.map_add_eq_mul]
    have e2 : psi (i - 1) = psi i * (starRingEnd ℂ) (psi 1) := by
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
        Complex.inv_eq_conj hnorm]
    have key : (psi (i - 1)).re + (psi (i + 1)).re = 2 * (psi 1).re * (psi i).re := by
      rw [e1, e2]
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    simp only
    rw [key, ← hre]
    ring

/-- **Fiedler value of the cycle graph.** For `n ≥ 3`, the algebraic connectivity of `C n`,
i.e. the smallest eigenvalue of its Laplacian admitting an eigenvector orthogonal to the
constant vector (equivalently, the second-smallest Laplacian eigenvalue), equals
`2 - 2 * cos (2 * π / n)`. -/
