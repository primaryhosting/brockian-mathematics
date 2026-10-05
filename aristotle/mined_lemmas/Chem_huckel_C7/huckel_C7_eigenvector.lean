import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

lemma huckel_C7_eigenvector (k : ℕ) :
    ∃ v : ZMod 7 → ℂ, v ≠ 0 ∧
      C7adj.mulVec v = (2 * Real.cos (2 * Real.pi * k / 7) : ℂ) • v := by
  set y : ℂ := zeta7 ^ k with hy_def
  have hy7 : y ^ 7 = 1 := by
    rw [hy_def, ← pow_mul, mul_comm, pow_mul, zeta7_pow_seven, one_pow]
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy7
    simp at hy7
  refine ⟨fun i => y ^ i.val, ?_, ?_⟩
  · intro hcon
    simpa using congrFun hcon 0
  · funext i
    have hval1 : ((1 : ZMod 7)).val = 1 := rfl
    have hnext : y ^ ((i + 1 : ZMod 7)).val = y ^ i.val * y := by
      rw [pow_val_add hy7 i 1, hval1, pow_one]
    have hprev : y ^ ((i - 1 : ZMod 7)).val = y ^ i.val * y⁻¹ := by
      have h2 : y ^ ((i - 1 : ZMod 7) + 1).val = y ^ ((i - 1 : ZMod 7)).val * y := by
        rw [pow_val_add hy7 (i - 1) 1, hval1, pow_one]
      rw [sub_add_cancel] at h2
      rw [h2, mul_inv_cancel_right₀ hy0]
    rw [C7adj_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hnext, hprev, ← zeta7_pow_add_inv k]
    ring

/-- **Hückel theory for the C₇ cycle.**  The eigenvalues of the adjacency matrix of the
cycle graph `C₇` are exactly the numbers `2 cos (2πk/7)`, `k = 0, …, 6`. -/
