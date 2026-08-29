/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma huckel_C8_root (μ : ℂ) (v : ZMod 8 → ℂ) (hv0 : v ≠ 0) (hv : C8adj.mulVec v = μ • v) :
    μ * (μ ^ 2 - 2) * (μ ^ 2 - 4) = 0 := by
  have hpow : ∀ n : ℕ, (C8adj ^ n).mulVec v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm (μ ^ n) μ]
  have e6 : ((6 : Matrix (ZMod 8) (ZMod 8) ℂ) * C8adj ^ 3).mulVec v
      = (6 : ℂ) • (C8adj ^ 3).mulVec v := by
    rw [← Matrix.mulVec_mulVec]; simp
  have e8 : ((8 : Matrix (ZMod 8) (ZMod 8) ℂ) * C8adj).mulVec v = (8 : ℂ) • C8adj.mulVec v := by
    rw [← Matrix.mulVec_mulVec]; simp
  have hmain : μ ^ 5 • v = (6 : ℂ) • (μ ^ 3 • v) - (8 : ℂ) • (μ • v) := by
    have := congrArg (fun M : Matrix (ZMod 8) (ZMod 8) ℂ => M.mulVec v) C8adj_pow_five
    simp only [Matrix.sub_mulVec, e6, e8, hpow, hv] at this
    simpa using this
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  have hj' := congrFun hmain j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hj'
  have : (μ * (μ ^ 2 - 2) * (μ ^ 2 - 4)) * v j = 0 := by linear_combination hj'
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hj

/-- **Hückel theory for the cyclic polyene C₈.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₈` (i.e. it admits a nonzero eigenvector) if and only if
`μ = 2 cos (2πk/8)` for some `k ∈ {0, …, 7}`. -/
