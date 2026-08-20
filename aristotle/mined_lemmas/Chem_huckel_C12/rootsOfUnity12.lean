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

lemma rootsOfUnity12 :
    {z : ℂ | z ^ 12 = 1}
      = Set.range (fun k : Fin 12 => Complex.exp (2 * Real.pi * Complex.I * k / 12)) := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12)) 12 :=
    Complex.isPrimitiveRoot_exp 12 (by norm_num)
  have hpow : ∀ k : ℕ, (Complex.exp (2 * Real.pi * Complex.I / 12)) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * k / 12) := by
    intro k
    rw [← Complex.exp_nat_mul]
    ring_nf
  apply Set.eq_of_subset_of_subset
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := hprim.eq_pow_of_pow_eq_one hz
    refine ⟨⟨i, hi⟩, ?_⟩
    show Complex.exp (2 * Real.pi * Complex.I * ((⟨i, hi⟩ : Fin 12) : ℕ) / 12) = z
    rw [Fin.val_mk, ← hpow i, hzi]
  · rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← hpow (k : ℕ), ← pow_mul, mul_comm (k : ℕ) 12, pow_mul, hprim.pow_eq_one, one_pow]

/-- For a `12`-th root of unity written as `exp (2πik/12)`, the value `z + z¹¹ = z + z⁻¹`
is `2 cos (2πk/12)`. -/
