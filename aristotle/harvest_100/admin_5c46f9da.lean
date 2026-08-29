/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/
noncomputable def zeta11 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `Fin 11`
(where addition is taken modulo `11`): vertices `i` and `j` are adjacent iff `j = i + 1`
or `i = j + 1`. -/
def C11adj : Matrix (Fin 11) (Fin 11) ℂ :=
  fun i j => if j = i + 1 ∨ i = j + 1 then 1 else 0

/-- The Hückel eigenvalues of `C₁₁` : `2 cos (2πk/11)`, `k = 0, …, 10`. -/
noncomputable def C11eig (k : Fin 11) : ℝ := 2 * Real.cos (2 * Real.pi * k / 11)

/-- The (discrete Fourier / Vandermonde) matrix diagonalizing `C11adj`. -/
noncomputable def C11fourier : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.vandermonde (fun k : Fin 11 => zeta11 ^ (k : ℕ))

theorem isPrimitiveRoot_zeta11 : IsPrimitiveRoot zeta11 11 := by
  have := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  simpa [zeta11] using this

theorem zeta11_pow_eleven : zeta11 ^ 11 = 1 := isPrimitiveRoot_zeta11.pow_eq_one

theorem zeta11_pow_congr {m n : ℕ} (h : m % 11 = n % 11) : zeta11 ^ m = zeta11 ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 11]
  conv_rhs => rw [← Nat.div_add_mod n 11]
  rw [pow_add, pow_add, pow_mul, zeta11_pow_eleven, one_pow, one_mul, h]

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/11)`. -/
theorem zeta11_pow_add_inv (k : ℕ) :
    zeta11 ^ k + zeta11 ^ (10 * k) = ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / 11 with hθ
  have h1 : zeta11 ^ k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta11, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hprod : zeta11 ^ k * zeta11 ^ (10 * k) = 1 := by
    rw [← pow_add, show k + 10 * k = 11 * k by ring, pow_mul, zeta11_pow_eleven, one_pow]
  have h2 : zeta11 ^ (10 * k) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    have hinv : (zeta11 ^ k)⁻¹ = zeta11 ^ (10 * k) := inv_eq_of_mul_eq_one_right hprod
    rw [← hinv, h1, ← Complex.exp_neg]
    ring_nf
  rw [h1, h2, ← Complex.two_cos, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

theorem C11fourier_apply (k i : Fin 11) : C11fourier k i = zeta11 ^ ((k : ℕ) * (i : ℕ)) := by
  rw [C11fourier, Matrix.vandermonde_apply, ← pow_mul]

theorem C11adj_apply (i j : Fin 11) :
    C11adj i j = (if i = j - 1 then 1 else 0) + (if i = j + 1 then 1 else 0) := by
  have hd1 : ∀ i j : Fin 11, (j = i + 1) ↔ (i = j - 1) := by decide
  have hd2 : ∀ j : Fin 11, (j - 1 : Fin 11) ≠ j + 1 := by decide
  rcases eq_or_ne i (j - 1) with h1 | h1
  · have h2 : i ≠ j + 1 := by rw [h1]; exact hd2 j
    have h3 : j = i + 1 := (hd1 i j).mpr h1
    simp [C11adj, h1, h2, h3]
  · rcases eq_or_ne i (j + 1) with h2 | h2
    · have h3 : ¬ (j = i + 1) := fun h => h1 ((hd1 i j).mp h)
      simp [C11adj, h1, h2, h3]
    · have h3 : ¬ (j = i + 1) := fun h => h1 ((hd1 i j).mp h)
      simp [C11adj, h1, h2, h3]

theorem C11fourier_mul_adj :
    C11fourier * C11adj = Matrix.diagonal (fun k => ((C11eig k : ℝ) : ℂ)) * C11fourier := by
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  have hpt : ∀ i : Fin 11, C11fourier k i * C11adj i j
      = (if i = j - 1 then zeta11 ^ ((k : ℕ) * (i : ℕ)) else 0)
        + (if i = j + 1 then zeta11 ^ ((k : ℕ) * (i : ℕ)) else 0) := by
    intro i
    rw [C11adj_apply, C11fourier_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => zeta11 ^ ((k : ℕ) * (i : ℕ))),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => zeta11 ^ ((k : ℕ) * (i : ℕ)))]
  simp only [Finset.mem_univ, if_true]
  have hm : ((j - 1 : Fin 11) : ℕ) = (j.val + 10) % 11 := by simp [Fin.sub_def]; omega
  have hp : ((j + 1 : Fin 11) : ℕ) = (j.val + 1) % 11 := by simp [Fin.add_def]
  have e1 : zeta11 ^ ((k : ℕ) * ((j - 1 : Fin 11) : ℕ)) = zeta11 ^ ((k : ℕ) * (j.val + 10)) := by
    apply zeta11_pow_congr
    rw [hm]
    simp [Nat.mul_mod]
  have e2 : zeta11 ^ ((k : ℕ) * ((j + 1 : Fin 11) : ℕ)) = zeta11 ^ ((k : ℕ) * (j.val + 1)) := by
    apply zeta11_pow_congr
    rw [hp]
    simp [Nat.mul_mod]
  rw [e1, e2, show (k : ℕ) * (j.val + 10) = (k : ℕ) * j.val + 10 * (k : ℕ) by ring,
    show (k : ℕ) * (j.val + 1) = (k : ℕ) * j.val + (k : ℕ) by ring, pow_add, pow_add, C11eig]
  rw [← zeta11_pow_add_inv (k : ℕ)]
  push_cast
  ring

theorem C11fourier_det_ne_zero : C11fourier.det ≠ 0 := by
  rw [C11fourier, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  intro h
  have h1 : zeta11 ^ (j : ℕ) = zeta11 ^ (i : ℕ) := sub_eq_zero.mp h
  have h2 : (j : ℕ) = (i : ℕ) := isPrimitiveRoot_zeta11.pow_inj j.isLt i.isLt h1
  exact absurd (Fin.ext h2) (Fin.ne_of_gt hj)

/-- **Hückel theory for the cycle `C₁₁`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₁` is `∏_{k=0}^{10} (X - 2 cos (2πk/11))`, i.e. the adjacency
eigenvalues of `C₁₁` are exactly `2 cos (2πk/11)` for `k = 0, …, 10` (with multiplicity). -/
theorem huckel_C11 :
    C11adj.charpoly =
      ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ)) := by
  have hF : IsUnit C11fourier.det := isUnit_iff_ne_zero.mpr C11fourier_det_ne_zero
  have hA : C11adj
      = C11fourier⁻¹ * (Matrix.diagonal (fun k => ((C11eig k : ℝ) : ℂ)) * C11fourier) := by
    rw [← C11fourier_mul_adj, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hF, Matrix.one_mul]
  rw [hA, Matrix.charpoly_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF,
    Matrix.mul_one, Matrix.charpoly_diagonal]
  rfl

/-- The spectrum of the adjacency matrix of `C₁₁` is exactly the set of numbers
`2 cos (2πk/11)`, `k = 0, …, 10`. -/
theorem huckel_C11_spectrum :
    spectrum ℂ C11adj =
      Set.range (fun k : Fin 11 => ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ)) := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero, Set.mem_range]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

