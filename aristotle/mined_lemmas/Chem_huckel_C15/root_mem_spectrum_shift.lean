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

lemma root_mem_spectrum_shift {ν : ℂ} (hν : ν ^ 15 = 1) : ν ^ 14 ∈ spectrum ℂ shift := by
  have hmod : ∀ a : ℕ, ν ^ a = ν ^ (a % 15) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a 15]
    rw [pow_add, pow_mul, hν, one_pow, one_mul]
  rw [spectrum.mem_iff]
  intro h
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h
  apply h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => ν ^ (i.val), ?_, ?_⟩
  · intro hzero
    have h0 := congrFun hzero 0
    simp at h0
  · funext i
    have hshift := shift_mulVec (fun i : Fin 15 => ν ^ (i.val)) i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Algebra.algebraMap_eq_smul_one,
      smul_one_mulVec, hshift, Pi.zero_apply]
    rw [← pow_add, hmod (14 + i.val), hmod ((i - 1 : Fin 15)).val]
    have hval : ((i - 1 : Fin 15)).val = (i.val + 14) % 15 := by omega
    rw [hval, Nat.mod_mod_of_dvd _ (dvd_refl 15), sub_eq_zero]
    congr 1

/-- The spectrum of the cyclic shift matrix is exactly the set of 15-th roots of unity. -/
