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

set_option grind.warning false

/-!
# Hückel theory for the cyclic polyene C₁₆

The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of an annulene with
16 carbon atoms, up to the usual affine normalisation `α + β x`) has characteristic
polynomial `∏ k < 16, (X - 2 cos (2πk/16))`, so its eigenvalues are exactly the
numbers `2 cos (2πk/16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix
`U j k = ω^(jk)`, where `ω = exp (2πi/16)`.
-/

namespace Chem

open Polynomial Matrix Complex

/-- The adjacency (Hückel) matrix of the cycle graph `C₁₆`, over `ℂ`. -/
noncomputable def C16 : Matrix (Fin 16) (Fin 16) ℂ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℂ

/-- A primitive 16-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The (unnormalised) discrete Fourier matrix of size 16. -/
noncomputable def dftU : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun j k => om ^ (j.val * k.val)

/-- The inverse discrete Fourier matrix of size 16. -/
noncomputable def dftV : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun j k => (16 : ℂ)⁻¹ * om⁻¹ ^ (j.val * k.val)

/-- The diagonal matrix of Hückel eigenvalues of `C₁₆`. -/
noncomputable def Dg : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.diagonal fun k : Fin 16 => ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ)

lemma om_primitiveRoot : IsPrimitiveRoot om 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [om] using this

lemma om_pow_sixteen : om ^ (16 : ℕ) = 1 := om_primitiveRoot.pow_eq_one

lemma om_pow_mod (a : ℕ) : om ^ a = om ^ (a % 16) := by
  conv_lhs => rw [← Nat.div_add_mod a 16]
  rw [pow_add, pow_mul, om_pow_sixteen, one_pow, one_mul]

lemma om_pow_modEq {a b : ℕ} (h : a ≡ b [MOD 16]) : om ^ a = om ^ b := by
  rw [om_pow_mod a, om_pow_mod b, h]

lemma om_inv_eq : om⁻¹ = om ^ (15 : ℕ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ']
  exact om_pow_sixteen

/-- Geometric sums of powers of `om`: they vanish unless the exponent is a multiple of 16. -/
lemma sum_om_pow (m : ℕ) :
    ∑ k : Fin 16, (om ^ m) ^ (k.val) = if m % 16 = 0 then (16 : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (om ^ m) ^ i) 16]
  by_cases h : m % 16 = 0
  · have h1 : om ^ m = 1 := by rw [om_pow_mod m, h, pow_zero]
    simp [h1, h]
  · have hz : om ^ m ≠ 1 := by
      intro hc
      have hdvd : 16 ∣ m := om_primitiveRoot.dvd_of_pow_eq_one m hc
      omega
    rw [geom_sum_eq hz]
    have h16 : (om ^ m) ^ 16 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, om_pow_sixteen, one_pow]
    simp [h16, h]

lemma dftU_mul_dftV : dftU * dftV = 1 := by
  have key : ∀ j l : Fin 16, ((j.val + 15 * l.val) % 16 = 0 ↔ j = l) := by decide
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 16, dftU j k * dftV k l
      = (16 : ℂ)⁻¹ * (om ^ (j.val + 15 * l.val)) ^ (k.val) := by
    intro k
    simp only [dftU, dftV, Matrix.of_apply, om_inv_eq, ← pow_mul]
    rw [mul_comm ((16 : ℂ)⁻¹) _, ← mul_assoc, ← pow_add,
      show j.val * k.val + 15 * (k.val * l.val) = (j.val + 15 * l.val) * k.val from by ring,
      mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_om_pow, Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos ((key j l).mpr h), if_pos h]; norm_num
  · rw [if_neg (fun hc => h ((key j l).mp hc)), if_neg h]; ring

lemma dftV_mul_dftU : dftV * dftU = 1 := by
  have key : ∀ j l : Fin 16, ((15 * j.val + l.val) % 16 = 0 ↔ j = l) := by decide
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 16, dftV j k * dftU k l
      = (16 : ℂ)⁻¹ * (om ^ (15 * j.val + l.val)) ^ (k.val) := by
    intro k
    simp only [dftU, dftV, Matrix.of_apply, om_inv_eq, ← pow_mul]
    rw [mul_assoc, ← pow_add,
      show 15 * (j.val * k.val) + k.val * l.val = (15 * j.val + l.val) * k.val from by ring]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_om_pow, Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos ((key j l).mpr h), if_pos h]; norm_num
  · rw [if_neg (fun hc => h ((key j l).mp hc)), if_neg h]; ring

/-- The eigenvalue `2 cos (2πk/16)` written in terms of `om`. -/
lemma two_cos_eq (k : Fin 16) :
    ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ) = om ^ k.val + om ^ (15 * k.val) := by
  set x : ℝ := 2 * Real.pi * k.val / 16 with hx
  have h1 : om ^ k.val = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul, hx]
    congr 1
    push_cast
    ring
  have h2 : om ^ (15 * k.val) = Complex.exp (-((x : ℂ) * Complex.I)) := by
    have hmul : om ^ k.val * om ^ (15 * k.val) = 1 := by
      rw [← pow_add, show k.val + 15 * k.val = 16 * k.val from by ring, pow_mul, om_pow_sixteen,
        one_pow]
    rw [(inv_eq_of_mul_eq_one_right hmul).symm, h1, ← Complex.exp_neg]
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- The entries of the adjacency matrix of `C₁₆`: vertex `j` is adjacent exactly to `j ± 1`. -/
lemma C16_apply (j l : Fin 16) :
    C16 j l = (if l = j + 1 then (1 : ℂ) else 0) + (if l = j - 1 then 1 else 0) := by
  have hd : ∀ j l : Fin 16, ((SimpleGraph.cycleGraph 16).Adj j l ↔ (l = j + 1 ∨ l = j - 1)) := by
    decide
  have hne : ∀ j : Fin 16, (j + 1 : Fin 16) ≠ j - 1 := by decide
  rw [C16, SimpleGraph.adjMatrix_apply]
  by_cases h1 : l = j + 1
  · have h2 : l ≠ j - 1 := by rw [h1]; exact hne j
    rw [if_pos ((hd j l).mpr (Or.inl h1)), if_pos h1, if_neg h2]; ring
  · by_cases h2 : l = j - 1
    · rw [if_pos ((hd j l).mpr (Or.inr h2)), if_neg h1, if_pos h2]; ring
    · rw [if_neg (fun hc => ((hd j l).mp hc).elim h1 h2), if_neg h1, if_neg h2]
      ring

/-- The Fourier basis diagonalises the circulant matrix `C16`. -/
lemma C16_mul_dftU : C16 * dftU = dftU * Dg := by
  have hsucc : ∀ j : Fin 16, (j + 1 : Fin 16).val ≡ j.val + 1 [MOD 16] := by decide
  have hpred : ∀ j : Fin 16, (j - 1 : Fin 16).val ≡ j.val + 15 [MOD 16] := by decide
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ l : Fin 16, C16 j l * dftU l k
      = om ^ ((j + 1 : Fin 16).val * k.val) + om ^ ((j - 1 : Fin 16).val * k.val) := by
    simp only [C16_apply, dftU, Matrix.of_apply, add_mul, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_add_distrib]
    simp
  have hR : ∑ l : Fin 16, dftU j l * Dg l k
      = om ^ (j.val * k.val) * ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ) := by
    simp only [dftU, Dg, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero]
    simp
  rw [hL, hR, two_cos_eq, mul_add, ← pow_add, ← pow_add]
  congr 1
  · exact om_pow_modEq (((hsucc j).mul_right k.val).trans (by rw [Nat.add_mul, one_mul]))
  · exact om_pow_modEq (((hpred j).mul_right k.val).trans (by rw [Nat.add_mul]))

/-- `dftU` as a unit of the matrix ring. -/
noncomputable def dftUnit : (Matrix (Fin 16) (Fin 16) ℂ)ˣ :=
  ⟨dftU, dftV, dftU_mul_dftV, dftV_mul_dftU⟩

lemma C16_conj :
    C16 = (↑dftUnit : Matrix (Fin 16) (Fin 16) ℂ) * Dg
      * (↑dftUnit⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
  show C16 = dftU * Dg * dftV
  rw [← C16_mul_dftU, mul_assoc, dftU_mul_dftV, mul_one]

/-- **Hückel spectrum of C₁₆**: the characteristic polynomial of the adjacency matrix of
the cycle graph `C₁₆` factors as `∏ k < 16, (X - 2 cos (2πk/16))`; i.e. the adjacency
eigenvalues of `C₁₆` are exactly `2 cos (2πk/16)` for `k = 0, …, 15`. -/
theorem huckel_C16 :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ).charpoly =
      ∏ k : Fin 16, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ)) := by
  show C16.charpoly = _
  rw [C16_conj, Matrix.charpoly_units_conj, Dg, Matrix.charpoly_diagonal]

/-- The Fourier vector `j ↦ ω^(jk)` is a nonzero eigenvector of the adjacency matrix of `C₁₆`
with eigenvalue `2 cos (2πk/16)`. -/
theorem huckel_C16_eigenvector (k : Fin 16) :
    (fun j : Fin 16 => om ^ (j.val * k.val)) ≠ 0 ∧
      ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) *ᵥ (fun j : Fin 16 => om ^ (j.val * k.val))
        = ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ) •
            (fun j : Fin 16 => om ^ (j.val * k.val)) := by
  refine ⟨?_, ?_⟩
  · intro hzero
    have h0 := congrFun hzero 0
    simp at h0
  funext j
  have h := congrFun (congrFun C16_mul_dftU j) k
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  have hC : ∀ x : Fin 16, SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 16) j x
      * om ^ (x.val * k.val) = C16 j x * dftU x k := fun _ => rfl
  rw [Finset.sum_congr rfl (fun x _ => hC x), h]
  simp only [Dg, Matrix.diagonal_apply, dftU, Matrix.of_apply]
  rw [Finset.sum_eq_single k] <;> simp +contextual [mul_comm]

/-- The spectrum of the adjacency matrix of `C₁₆` is exactly
`{2 cos (2πk/16) : k = 0, …, 15}`. -/
theorem huckel_C16_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : ℕ, k < 16 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 16) : ℝ) : ℂ)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C16]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.val, k.isLt, hk⟩
  · rintro ⟨k, hk, hμ⟩
    exact ⟨⟨k, hk⟩, by simpa using hμ⟩

end Chem

