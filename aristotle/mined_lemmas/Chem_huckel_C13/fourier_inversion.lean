import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma fourier_inversion (v : ZMod 13 → ℂ) (j : ZMod 13) :
    ∑ k : ZMod 13, e13 (k * j) * (∑ l : ZMod 13, e13 (-(k * l)) * v l) = 13 * v j := by
  have step : ∀ k : ZMod 13, e13 (k * j) * (∑ l : ZMod 13, e13 (-(k * l)) * v l)
      = ∑ l : ZMod 13, e13 (k * (j - l)) * v l := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, ← e13_add]
    congr 2
    ring
  simp_rw [step]
  rw [Finset.sum_comm]
  have hfac : ∀ l : ZMod 13, (∑ k : ZMod 13, e13 (k * (j - l)) * v l)
      = (if j - l = 0 then (13 : ℂ) else 0) * v l := by
    intro l
    rw [← Finset.sum_mul, e13_sum]
  simp_rw [hfac]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    have hjl : j - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
    simp [hjl]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Hückel theory for the cycle `C₁₃`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` if and only if `μ = 2 cos (2πk/13)` for some
`k ∈ {0, 1, …, 12}`. -/
