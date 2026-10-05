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

lemma sum_inv_eq_two_cos {y : ℂ} (hy : y ^ 7 = 1) :
    ∃ k : ℕ, k < 7 ∧ y + y⁻¹ = 2 * Real.cos (2 * Real.pi * k / 7) := by
  obtain ⟨k, hk, hyk⟩ := zeta7_isPrimitiveRoot.eq_pow_of_pow_eq_one hy
  exact ⟨k, hk, hyk ▸ zeta7_pow_add_inv k⟩

/-- For each `k`, the discrete plane wave `i ↦ ζ⁷ᵏⁱ` is an eigenvector of the adjacency
matrix of `C₇` with eigenvalue `2 cos (2πk/7)`. -/
