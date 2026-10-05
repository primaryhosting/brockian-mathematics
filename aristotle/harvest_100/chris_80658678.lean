/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/
noncomputable def C10adj : Matrix (Fin 10) (Fin 10) ℂ := adjMatrix ℂ (cycleGraph 10)

/-- The `k`-th Hückel eigenvalue of `C₁₀`, namely `2 cos (2πk/10)`. -/
noncomputable def huckelEigenvalue (k : Fin 10) : ℝ := 2 * Real.cos (2 * Real.pi * k / 10)

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

lemma zeta_pow_ten : zeta ^ 10 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_sub_ten {n : ℕ} (hn : 10 ≤ n) : zeta ^ n = zeta ^ (n - 10) := by
  conv_lhs => rw [show n = (n - 10) + 10 by omega]
  rw [pow_add, zeta_pow_ten, mul_one]

/-- `ζ^m + ζ^(10-m) = 2 cos (2πm/10)` for `m ≤ 10`. -/
lemma zeta_pow_add_zeta_pow (m : ℕ) (hm : m ≤ 10) :
    zeta ^ m + zeta ^ (10 - m) = 2 * (Real.cos (2 * Real.pi * m / 10) : ℝ) := by
  have h1 : zeta ^ m = Complex.exp ((2 * Real.pi * m / 10 : ℝ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hmul : zeta ^ m * zeta ^ (10 - m) = 1 := by
    rw [← pow_add, show m + (10 - m) = 10 by omega, zeta_pow_ten]
  have h2 : zeta ^ (10 - m) = Complex.exp (-((2 * Real.pi * m / 10 : ℝ) * Complex.I)) := by
    rw [Complex.exp_neg, ← h1]
    exact (DivisionMonoid.inv_eq_of_mul _ _ hmul).symm
  rw [h1, h2, Complex.ofReal_cos, Complex.two_cos, neg_mul]

/-- The (unnormalised) discrete Fourier matrix `U j k = ζ^{jk}`; it is a Vandermonde matrix in the
nodes `ζ^j`. -/
noncomputable def dftU : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.of fun j k : Fin 10 => zeta ^ (j.val * k.val)

lemma dftU_eq_vandermonde : dftU = Matrix.vandermonde (fun j : Fin 10 => zeta ^ (j : ℕ)) := by
  ext j k
  simp [dftU, Matrix.vandermonde_apply, ← pow_mul]

lemma dftU_isUnit : IsUnit dftU := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, dftU_eq_vandermonde]
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

/-- The diagonal matrix of Hückel eigenvalues of `C₁₀`. -/
noncomputable def C10diag : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.diagonal fun k : Fin 10 => ((huckelEigenvalue k : ℝ) : ℂ)

lemma C10diag_eq :
    C10diag = Matrix.diagonal fun k : Fin 10 => zeta ^ (k : ℕ) + zeta ^ (10 - (k : ℕ)) := by
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  rw [zeta_pow_add_zeta_pow (k : ℕ) (le_of_lt k.isLt)]
  simp [huckelEigenvalue]

/-- Every vertex of `C₁₀` has exactly two neighbours. -/
lemma cycleGraph10_card_neighbors (j : Fin 10) :
    ({x | (cycleGraph 10).Adj j x} : Finset (Fin 10)).card = 2 := by
  fin_cases j <;> decide

set_option maxHeartbeats 4000000 in
lemma C10adj_mul_dftU : C10adj * dftU = dftU * C10diag := by
  rw [C10diag_eq]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp +decide [C10adj, dftU, Matrix.mul_apply, Fin.sum_univ_succ,
      SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply, zeta_pow_sub_ten,
      cycleGraph10_card_neighbors] <;>
    ring_nf <;>
    simp only [zeta_pow_sub_ten, Nat.reduceSub, Nat.reduceLeDiff] <;>
    ring1

/-- The characteristic polynomial of the adjacency matrix of `C₁₀` splits as
`∏_{k=0}^{9} (X - 2 cos (2πk/10))`; in particular the ten Hückel eigenvalues, listed with
multiplicity, are `2 cos (2πk/10)` for `k = 0, …, 9`. -/
theorem huckel_C10_charpoly :
    C10adj.charpoly = ∏ k : Fin 10, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := dftU_isUnit
  set U : Matrix (Fin 10) (Fin 10) ℂ := (u : Matrix (Fin 10) (Fin 10) ℂ) with hU
  set Uinv : Matrix (Fin 10) (Fin 10) ℂ := ((u⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) :
    Matrix (Fin 10) (Fin 10) ℂ) with hUinv
  have hconj : C10adj = U * C10diag * Uinv := by
    have h : C10adj * U = U * C10diag := by rw [hU, hu]; exact C10adj_mul_dftU
    calc C10adj = C10adj * (U * Uinv) := by rw [hU, hUinv, u.mul_inv, mul_one]
      _ = (C10adj * U) * Uinv := by rw [mul_assoc]
      _ = U * C10diag * Uinv := by rw [h]
  rw [hconj, Matrix.charpoly_units_conj, C10diag, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₁₀`.**  The eigenvalues (i.e. the spectrum) of the adjacency matrix of
the cycle graph `C₁₀` are exactly the numbers `2 cos (2πk/10)` for `k = 0, 1, …, 9`. -/
theorem huckel_C10 (μ : ℂ) :
    μ ∈ spectrum ℂ C10adj ↔ ∃ k : Fin 10, μ = ((huckelEigenvalue k : ℝ) : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, huckel_C10_charpoly]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, sub_eq_zero.mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, sub_eq_zero.mpr hk⟩

end Chem

import Mathlib
open Matrix SimpleGraph

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

lemma zeta_pow_ten : zeta ^ 10 = 1 :=
  (Complex.isPrimitiveRoot_exp 10 (by norm_num)).pow_eq_one

lemma zeta_pow_sub_ten {n : ℕ} (hn : 10 ≤ n) : zeta ^ n = zeta ^ (n - 10) := by
  conv_lhs => rw [show n = (n - 10) + 10 by omega]
  rw [pow_add, zeta_pow_ten, mul_one]

lemma cycle10_card (j : Fin 10) : ({x | (cycleGraph 10).Adj j x} : Finset (Fin 10)).card = 2 := by
  fin_cases j <;> decide

noncomputable def dftU : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.of fun j k : Fin 10 => zeta ^ (j.val * k.val)

set_option maxHeartbeats 4000000 in
example : (adjMatrix ℂ (cycleGraph 10)) * dftU
    = dftU * Matrix.diagonal (fun k : Fin 10 => zeta ^ (k : ℕ) + zeta ^ (10 - (k : ℕ))) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp +decide [dftU, Matrix.mul_apply, Fin.sum_univ_succ,
      SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply, zeta_pow_sub_ten, cycle10_card] <;>
    ring_nf <;>
    simp only [zeta_pow_sub_ten, Nat.reduceSub, Nat.reduceLeDiff] <;>
    ring1

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

