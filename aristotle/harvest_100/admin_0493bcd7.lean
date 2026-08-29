import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including this
module docstring, so the header comment appears immediately after the single import.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₈`, over `ℂ`. -/
noncomputable def C8adj : Matrix (Fin 8) (Fin 8) ℂ := (cycleGraph 8).adjMatrix ℂ

/-- A primitive 8-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

lemma w_isPrimitiveRoot : IsPrimitiveRoot w 8 := by
  simpa [w] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

lemma w_pow_eight : w ^ 8 = 1 := w_isPrimitiveRoot.pow_eq_one

/-- The character `Fin 8 → ℂ`, `x ↦ ω ^ x`. -/
noncomputable def chi (x : Fin 8) : ℂ := w ^ (x : ℕ)

lemma w_pow_mod (n : ℕ) : w ^ (n % 8) = w ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 8]
  rw [pow_add, pow_mul, w_pow_eight, one_pow, one_mul]

lemma chi_add (x y : Fin 8) : chi (x + y) = chi x * chi y := by
  simp only [chi, Fin.add_def, ← pow_add]
  exact w_pow_mod _

lemma chi_mul_val (j k : Fin 8) : chi (j * k) = w ^ ((j : ℕ) * (k : ℕ)) := by
  simp only [chi, Fin.mul_def]
  exact w_pow_mod _

/-- The eigenvalues, as `ω ^ k + ω ^ (-k)`. -/
noncomputable def lam (k : Fin 8) : ℂ := chi k + chi (-k)

lemma chi_neg (k : Fin 8) : chi (-k) = (chi k)⁻¹ := by
  have hne : chi k ≠ 0 := by
    simp only [chi]
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  have : chi (-k) * chi k = 1 := by
    rw [← chi_add]
    simp [chi]
  field_simp at this ⊢
  linear_combination this

lemma lam_eq (k : Fin 8) : lam k = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) := by
  have hchi : chi k = Complex.exp ((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I) := by
    simp only [chi, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hchi' : chi (-k) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I)) := by
    rw [chi_neg, hchi, ← Complex.exp_neg]
  rw [lam, hchi, hchi']
  rw [Complex.ofReal_mul, Complex.ofReal_cos]
  rw [Complex.cos]
  push_cast
  ring_nf

/-- The (Vandermonde/DFT) matrix diagonalizing the adjacency matrix. -/
noncomputable def U : Matrix (Fin 8) (Fin 8) ℂ := Matrix.vandermonde (fun j : Fin 8 => w ^ (j : ℕ))

lemma U_apply (j k : Fin 8) : U j k = w ^ ((j : ℕ) * (k : ℕ)) := by
  simp [U, Matrix.vandermonde, ← pow_mul]

lemma U_det_ne_zero : U.det ≠ 0 := by
  rw [U, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  have hval := w_isPrimitiveRoot.pow_inj j.2 i.2 h
  have hj' : (i : ℕ) < (j : ℕ) := hj
  omega

lemma adj_mul_U : C8adj * U = U * Matrix.diagonal lam := by
  ext i k
  have hne : (i - 1 : Fin 8) ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hleft : ∑ j, C8adj i j * U j k = U (i - 1) k + U (i + 1) k := by
    rw [show (∑ j, C8adj i j * U j k) = (((cycleGraph 8).adjMatrix ℂ) *ᵥ fun j => U j k) i from rfl]
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
      Finset.sum_pair hne]
  rw [hleft]
  have hright : ∑ x, U i x * (Matrix.diagonal lam) x k = U i k * lam k := by
    simp [Matrix.diagonal_apply]
  rw [hright]
  have h1 : U (i - 1) k = chi ((i - 1) * k) := by rw [chi_mul_val, U_apply]
  have h2 : U (i + 1) k = chi ((i + 1) * k) := by rw [chi_mul_val, U_apply]
  have h3 : U i k = chi (i * k) := by rw [chi_mul_val, U_apply]
  rw [h1, h2, h3, lam]
  have e1 : (i - 1) * k = i * k + (-k) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have e2 : (i + 1) * k = i * k + k := by rw [add_mul, one_mul]
  rw [e1, e2, chi_add, chi_add]
  ring

/-- The characteristic polynomial of the adjacency matrix of `C₈` splits as the product over
`k = 0, …, 7` of `X - 2cos(2πk/8)`, and the spectrum is exactly the set of these numbers:
the Hückel eigenvalues of cyclooctatetraene. -/
theorem huckel_C8 :
    ((cycleGraph 8).adjMatrix ℂ).charpoly
        = ∏ k : Fin 8, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ))
      ∧ spectrum ℂ ((cycleGraph 8).adjMatrix ℂ)
        = {z : ℂ | ∃ k : Fin 8, z = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ)} := by
  have hcp : ((cycleGraph 8).adjMatrix ℂ).charpoly
      = ∏ k : Fin 8, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ)) := by
    have hU : IsUnit U.det := isUnit_iff_ne_zero.mpr U_det_ne_zero
    set M : (Matrix (Fin 8) (Fin 8) ℂ)ˣ := Matrix.nonsingInvUnit U hU with hM
    have hMv : (M : Matrix (Fin 8) (Fin 8) ℂ) = U := rfl
    have hconj : C8adj = (M : Matrix (Fin 8) (Fin 8) ℂ) * Matrix.diagonal lam
        * ((M⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ) : Matrix (Fin 8) (Fin 8) ℂ) := by
      have hinv : (M : Matrix (Fin 8) (Fin 8) ℂ)
          * ((M⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ) : Matrix (Fin 8) (Fin 8) ℂ) = 1 := M.mul_inv
      calc C8adj = C8adj * ((M : Matrix (Fin 8) (Fin 8) ℂ) * (↑M⁻¹)) := by rw [hinv, mul_one]
        _ = (C8adj * U) * (↑M⁻¹ : Matrix (Fin 8) (Fin 8) ℂ) := by rw [hMv, mul_assoc]
        _ = _ := by rw [adj_mul_U, hMv, mul_assoc]
    have := Matrix.charpoly_units_conj M (Matrix.diagonal lam)
    rw [← hconj] at this
    rw [show ((cycleGraph 8).adjMatrix ℂ) = C8adj from rfl, this, Matrix.charpoly_diagonal]
    exact Finset.prod_congr rfl fun k _ => by rw [lam_eq]
  refine ⟨hcp, ?_⟩
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hcp]
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero]

/-- Explicit evaluation of the eight Hückel eigenvalues of `C₈` (cyclooctatetraene):
`2, √2, 0, -√2, -2, -√2, 0, √2`. -/
lemma cos_values (k : Fin 8) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 8)
      ∈ ({2, Real.sqrt 2, 0, -Real.sqrt 2, -2} : Set ℝ) := by
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  fin_cases k <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  · left
    rw [show (2 * Real.pi * ((0 : ℕ) : ℝ) / 8 : ℝ) = 0 by norm_num, Real.cos_zero]; norm_num
  · right; left
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 8 : ℝ) = Real.pi / 4 by norm_num; ring, h4]; ring
  · right; right; left
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 8 : ℝ) = Real.pi / 2 by norm_num; ring,
      Real.cos_pi_div_two]; ring
  · right; right; right; left
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 8 : ℝ) = Real.pi - Real.pi / 4 by norm_num; ring,
      Real.cos_pi_sub, h4]; ring
  · right; right; right; right
    rw [show (2 * Real.pi * ((4 : ℕ) : ℝ) / 8 : ℝ) = Real.pi by norm_num; ring, Real.cos_pi]
    norm_num
  · right; right; right; left
    rw [show (2 * Real.pi * ((5 : ℕ) : ℝ) / 8 : ℝ) = Real.pi - (-(Real.pi / 4)) by
      norm_num; ring, Real.cos_pi_sub, Real.cos_neg, h4]; ring
  · right; right; left
    rw [show (2 * Real.pi * ((6 : ℕ) : ℝ) / 8 : ℝ) = Real.pi - (-(Real.pi / 2)) by
      norm_num; ring, Real.cos_pi_sub, Real.cos_neg, Real.cos_pi_div_two]; ring
  · right; left
    rw [show (2 * Real.pi * ((7 : ℕ) : ℝ) / 8 : ℝ) = 2 * Real.pi - Real.pi / 4 by
      norm_num; ring, Real.cos_two_pi_sub, h4]; ring

/-- Consequence of `huckel_C8`: the spectrum of the adjacency matrix of `C₈` is exactly
`{2, √2, 0, -√2, -2}` (the Hückel π-orbital energies of cyclooctatetraene in units of β,
relative to α). -/
theorem huckel_C8_spectrum_explicit :
    spectrum ℂ ((cycleGraph 8).adjMatrix ℂ)
      = {2, ((Real.sqrt 2 : ℝ) : ℂ), 0, -((Real.sqrt 2 : ℝ) : ℂ), -2} := by
  rw [huckel_C8.2]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have := cos_values k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h | h | h <;> rw [h] <;> push_cast <;> simp
  · have h0 : ((2 * Real.cos (2 * Real.pi * ((0 : Fin 8) : ℕ) / 8) : ℝ) : ℂ) = 2 := by
      norm_num
    have h1 : ((2 * Real.cos (2 * Real.pi * ((1 : Fin 8) : ℕ) / 8) : ℝ) : ℂ)
        = ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [show (2 * Real.pi * ((1 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 4 by norm_num; ring,
        Real.cos_pi_div_four]
      push_cast; ring
    have h2 : ((2 * Real.cos (2 * Real.pi * ((2 : Fin 8) : ℕ) / 8) : ℝ) : ℂ) = 0 := by
      rw [show (2 * Real.pi * ((2 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 2 by norm_num; ring,
        Real.cos_pi_div_two]
      norm_num
    have h3 : ((2 * Real.cos (2 * Real.pi * ((3 : Fin 8) : ℕ) / 8) : ℝ) : ℂ)
        = -((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [show (2 * Real.pi * ((3 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi - Real.pi / 4 by
        norm_num; ring, Real.cos_pi_sub, Real.cos_pi_div_four]
      push_cast; ring
    have h4 : ((2 * Real.cos (2 * Real.pi * ((4 : Fin 8) : ℕ) / 8) : ℝ) : ℂ) = -2 := by
      rw [show (2 * Real.pi * ((4 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi by norm_num; ring, Real.cos_pi]
      norm_num
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
    · exact ⟨2, h2.symm⟩
    · exact ⟨3, h3.symm⟩
    · exact ⟨4, h4.symm⟩

end Chem

