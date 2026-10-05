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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₂H₁₂` uses the adjacency matrix of the cycle
graph `C₁₂`.  We show that the characteristic polynomial of this adjacency matrix is
`∏ k, (X - 2 cos (2πk/12))`, and consequently that the eigenvalues of the adjacency matrix
are exactly the numbers `2 cos (2πk/12)`, `k = 0, …, 11`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix
`F j k = ω ^ (j * k)`, where `ω = exp (2πi/12)`.
-/

namespace Chem

open Complex Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₁₂`, viewed over `ℂ`. -/
noncomputable def adjC12 : Matrix (Fin 12) (Fin 12) ℂ :=
  SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 12)

/-- The `k`-th Hückel eigenvalue of `C₁₂`. -/
noncomputable def huckelEigenvalue (k : Fin 12) : ℝ := 2 * Real.cos (2 * Real.pi * k / 12)

/-- A primitive 12-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- The (unnormalised) discrete Fourier matrix. -/
noncomputable def dftF : Matrix (Fin 12) (Fin 12) ℂ := Matrix.of fun j k => w ^ (j.val * k.val)

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def eigD : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.diagonal fun k => ((huckelEigenvalue k : ℝ) : ℂ)

lemma w_pow_twelve : w ^ 12 = 1 := by
  rw [w, ← Complex.exp_nat_mul,
    show ((12 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 12) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma w_pow_congr {a b : ℕ} (h : a % 12 = b % 12) : w ^ a = w ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 12, pow_add, pow_mul, w_pow_twelve, one_pow, one_mul, h]
  conv_rhs => rw [← Nat.div_add_mod b 12, pow_add, pow_mul, w_pow_twelve, one_pow, one_mul]

lemma w_pow_eq_exp (m : ℕ) :
    w ^ m = Complex.exp (((2 * Real.pi * m / 12 : ℝ) : ℂ) * Complex.I) := by
  rw [w, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ω ^ m + ω ^ (-m) = 2 cos (2πm/12)`. -/
lemma w_pow_add_w_pow (m : ℕ) :
    w ^ m + w ^ (11 * m) = ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ) := by
  have h1 : w ^ m * w ^ (11 * m) = 1 := by
    rw [← pow_add, show m + 11 * m = 12 * m by ring, pow_mul, w_pow_twelve, one_pow]
  have h2 : w ^ (11 * m) = (w ^ m)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  rw [h2, w_pow_eq_exp, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, ← neg_mul]
  ring

lemma w_isPrimitiveRoot : IsPrimitiveRoot w 12 := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  rw [w]
  convert h using 2

lemma dftF_eq_vandermonde : dftF = Matrix.vandermonde (fun j : Fin 12 => w ^ (j : ℕ)) := by
  ext j k
  simp [dftF, Matrix.vandermonde, pow_mul]

lemma dftF_det_ne_zero : dftF.det ≠ 0 := by
  rw [dftF_eq_vandermonde, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  intro h
  have h2 : w ^ (j : ℕ) = w ^ (i : ℕ) := by linear_combination h
  have h3 := w_isPrimitiveRoot.pow_inj j.isLt i.isLt h2
  have h4 : (i : ℕ) < (j : ℕ) := hj
  omega

/-- Multiplying by the adjacency matrix of `C₁₂` sums the two neighbouring values. -/
lemma adjC12_mulVec_apply (g : Fin 12 → ℂ) (j : Fin 12) :
    ∑ i, adjC12 j i * g i = g (j + 1) + g (j - 1) := by
  have hf : (Finset.univ.filter fun i => (SimpleGraph.cycleGraph 12).Adj j i) = {j + 1, j - 1} := by
    revert j; decide
  have hne : j + 1 ≠ j - 1 := by revert j; decide
  simp only [adjC12, SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul,
    ← Finset.sum_filter, hf]
  rw [Finset.sum_pair hne]

/-- The Fourier matrix diagonalises the adjacency matrix. -/
lemma adjC12_mul_dftF : adjC12 * dftF = dftF * eigD := by
  have hadd : ∀ j : Fin 12, ((j + 1 : Fin 12) : ℕ) = (j.val + 1) % 12 := by decide
  have hsub : ∀ j : Fin 12, ((j - 1 : Fin 12) : ℕ) = (j.val + 11) % 12 := by decide
  ext j k
  rw [Matrix.mul_apply, adjC12_mulVec_apply (fun i => dftF i k) j, eigD, Matrix.mul_diagonal]
  show w ^ (((j + 1 : Fin 12) : ℕ) * k.val) + w ^ (((j - 1 : Fin 12) : ℕ) * k.val)
      = w ^ (j.val * k.val) * ((huckelEigenvalue k : ℝ) : ℂ)
  have e1 : w ^ (((j + 1 : Fin 12) : ℕ) * k.val) = w ^ (j.val * k.val + k.val) := by
    refine w_pow_congr ?_
    rw [hadd]
    simp [add_mul]
  have e2 : w ^ (((j - 1 : Fin 12) : ℕ) * k.val) = w ^ (j.val * k.val + 11 * k.val) := by
    refine w_pow_congr ?_
    rw [hsub]
    simp [add_mul]
  rw [e1, e2, pow_add, pow_add, huckelEigenvalue, ← w_pow_add_w_pow k.val]
  ring

/-- The characteristic polynomial of the adjacency matrix of `C₁₂`. -/
lemma charpoly_adjC12 :
    adjC12.charpoly = ∏ k : Fin 12, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) := by
  have hdet : IsUnit dftF.det := isUnit_iff_ne_zero.mpr dftF_det_ne_zero
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det dftF).mpr hdet
  have hA : adjC12 = U.val * eigD * (U⁻¹).val := by
    rw [Matrix.coe_units_inv, hU, ← adjC12_mul_dftF, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  rw [hA, Matrix.charpoly_units_conj U eigD, eigD, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₁₂`.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₂` is `∏ k, (X - 2 cos (2πk/12))`; equivalently, the eigenvalues of the
adjacency matrix are exactly the numbers `2 cos (2πk/12)` for `k = 0, …, 11`. -/
theorem huckel_C12 :
    (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 12)).charpoly
        = ∏ k : Fin 12, (X - C ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ))
      ∧ ∀ μ : ℂ,
        (∃ v : Fin 12 → ℂ, v ≠ 0 ∧
            (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 12)) *ᵥ v = μ • v)
          ↔ ∃ k : Fin 12, μ = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) := by
  have hAdef : SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 12) = adjC12 := rfl
  have hchar := charpoly_adjC12
  rw [hAdef]
  refine ⟨hchar, fun μ => ?_⟩
  have hiff : (∃ v : Fin 12 → ℂ, v ≠ 0 ∧ adjC12 *ᵥ v = μ • v)
      ↔ (adjC12 - Matrix.scalar (Fin 12) μ).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [Matrix.sub_mulVec, sub_eq_zero]
    have hs : (Matrix.scalar (Fin 12) μ) *ᵥ v = μ • v := by
      ext i; simp [Matrix.scalar, Matrix.mulVec_diagonal]
    rw [hs]
  have hdet : (adjC12 - Matrix.scalar (Fin 12) μ).det = eval μ adjC12.charpoly := by
    rw [Matrix.eval_charpoly, show adjC12 - Matrix.scalar (Fin 12) μ
      = -(Matrix.scalar (Fin 12) μ - adjC12) from (neg_sub _ _).symm, Matrix.det_neg]
    norm_num
  rw [hiff, hdet, hchar]
  simp only [eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero, huckelEigenvalue]

end Chem

