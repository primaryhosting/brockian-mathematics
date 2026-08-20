import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` (the Hückel spectrum of a
15-membered annulene, in units of β above α) are exactly the numbers `2 cos (2πk/15)`
for `k = 0, …, 14`.

The proof writes the adjacency matrix as `S + S¹⁴`, where `S` is the cyclic shift permutation
matrix, identifies the spectrum of `S` with the set of 15-th roots of unity, and then applies
the polynomial spectral mapping theorem over `ℂ`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The cyclic shift permutation matrix on `Fin 15`: `shift i j = 1` iff `i - 1 = j`. -/

lemma spectrum_shift : spectrum ℂ shift = {ν : ℂ | ν ^ 15 = 1} := by
  ext ν
  constructor
  · intro hv
    have h := spectrum.pow_mem_pow shift 15 hv
    rw [shift_pow_fifteen, spectrum.one_eq] at h
    simpa using h
  · intro (hv : ν ^ 15 = 1)
    have h14 : (ν ^ 14) ^ 15 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]
    have := root_mem_spectrum_shift h14
    rwa [← pow_mul, show 14 * 14 = 15 * 13 + 1 by norm_num, pow_add, pow_mul, hv, one_pow, one_mul,
      pow_one] at this

/-- `exp (2πi/15)` is a 15-th root of unity. -/
