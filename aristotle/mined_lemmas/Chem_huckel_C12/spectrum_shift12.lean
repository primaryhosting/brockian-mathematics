import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₂`

We show that the eigenvalues (i.e. the spectrum) of the adjacency matrix of the cycle graph
`C₁₂`, viewed as a complex matrix indexed by `ZMod 12`, are exactly the numbers
`2 * cos (2 * π * k / 12)` for `k = 0, …, 11`.

The proof goes through the cyclic shift matrix `S` on `ZMod 12`: the adjacency matrix is
`S + S ^ 11`, the spectrum of `S` is the set of `12`-th roots of unity, and the polynomial
spectral mapping theorem over `ℂ` transports this to the adjacency matrix.
-/

namespace Chem

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod 12`. -/

lemma spectrum_shift12 : spectrum ℂ shift12 = {z : ℂ | z ^ 12 = 1} := by
  apply Set.eq_of_subset_of_subset
  · intro z hz
    have h1 : z ^ 12 ∈ spectrum ℂ (shift12 ^ 12) :=
      spectrum.pow_image_subset shift12 12 ⟨z, hz, rfl⟩
    rw [shift12_pow_12, spectrum.one_eq] at h1
    exact h1
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    rw [spectrum.mem_iff]
    intro hu
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
    apply hu
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun j => z ^ j.val, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · have pow_mod : ∀ m : ℕ, z ^ (m % 12) = z ^ m := by
        intro m
        conv_rhs => rw [← Nat.div_add_mod m 12]
        rw [pow_add, pow_mul, hz, one_pow, one_mul]
      have hval : ∀ i : ZMod 12, (i + 1).val = (i.val + 1) % 12 := by decide
      funext i
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hs : (shift12.mulVec fun j => z ^ j.val) i = z ^ (i + 1).val := by
        simp [Matrix.mulVec, shift12, dotProduct]
      rw [hs, hval i, pow_mod, pow_succ]
      ring

/-- The `12`-th roots of unity, described via the complex exponential. -/
