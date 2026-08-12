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

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ## Hückel theory for the cycle `C₁₁`

We compute the spectrum of the adjacency matrix of the cycle graph on 11 vertices by
diagonalising it with the discrete Fourier transform matrix. -/

/-- A primitive 11-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

lemma om_isPrimitiveRoot : IsPrimitiveRoot om 11 := by
  have h := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  simpa [om] using h

lemma om_pow_eleven : om ^ 11 = 1 := om_isPrimitiveRoot.pow_eq_one

lemma om_pow_mod (a : ℕ) : om ^ (a % 11) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 11]
  rw [pow_add, pow_mul, om_pow_eleven, one_pow, one_mul]

lemma om_pow_mod_mul (a b : ℕ) : om ^ (a % 11 * b) = om ^ (a * b) := by
  rw [← om_pow_mod (a % 11 * b), ← om_pow_mod (a * b), Nat.mod_mul_mod]

lemma om_pow_eq_exp (n : ℕ) :
    om ^ n = Complex.exp (((2 * Real.pi * n / 11 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The two "neighbouring" powers of `om` add up to `2 cos (2πl/11)`. -/
lemma om_pow_add_om_pow (l : ℕ) :
    om ^ l + om ^ (10 * l) = ((2 * Real.cos (2 * Real.pi * l / 11) : ℝ) : ℂ) := by
  rw [om_pow_eq_exp, om_pow_eq_exp]
  push_cast
  rw [Complex.two_cos]
  have h : 2 * (Real.pi : ℂ) * (10 * l) / 11 * Complex.I
      = (l : ℂ) * (2 * Real.pi * Complex.I) + -(2 * (Real.pi : ℂ) * l / 11) * Complex.I := by
    ring
  rw [h, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]

/-- The sum of all 11-th powers of a nontrivial 11-th root of unity vanishes. -/
lemma sum_pow_eq_zero (z : ℂ) (hz : z ^ 11 = 1) (hne : z ≠ 1) : ∑ k : Fin 11, z ^ k.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 11]
  have h : (∑ i ∈ Finset.range 11, z ^ i) * (z - 1) = 0 := by rw [geom_sum_mul, hz, sub_self]
  rcases mul_eq_zero.mp h with h1 | h2
  · exact h1
  · exact absurd (sub_eq_zero.mp h2) hne

/-- The discrete Fourier transform matrix on `Fin 11`. -/
noncomputable def Fm : Matrix (Fin 11) (Fin 11) ℂ := fun j k => om ^ (j.val * k.val)

/-- The inverse discrete Fourier transform matrix on `Fin 11`. -/
noncomputable def Gm : Matrix (Fin 11) (Fin 11) ℂ :=
  fun j k => (11 : ℂ)⁻¹ * om ^ (10 * (j.val * k.val))

/-- The diagonal matrix of Hückel eigenvalues of the cycle `C₁₁`. -/
noncomputable def Dm : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.diagonal fun k : Fin 11 => ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ)

lemma Fm_mul_Gm : Fm * Gm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 11,
      Fm j k * Gm k l = (11 : ℂ)⁻¹ * (om ^ (j.val + 10 * l.val)) ^ k.val := by
    intro k
    simp only [Fm, Gm, ← pow_mul]
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum]
  by_cases h : j = l
  · subst h
    have hz : om ^ (j.val + 10 * j.val) = 1 := by
      have h11 : j.val + 10 * j.val = 11 * j.val := by ring
      rw [h11, pow_mul, om_pow_eleven, one_pow]
    rw [hz]
    simp
  · have hz : om ^ (j.val + 10 * l.val) ≠ 1 := by
      intro hc
      have hdvd := (om_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp hc
      have hj := j.isLt
      have hl := l.isLt
      have hjl : j.val ≠ l.val := fun hh => h (Fin.ext hh)
      omega
    have h11 : (om ^ (j.val + 10 * l.val)) ^ 11 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, om_pow_eleven, one_pow]
    rw [sum_pow_eq_zero _ h11 hz]
    simp [h]

lemma adjMatrix_mul_Fm : (cycleGraph 11).adjMatrix ℂ * Fm = Fm * Dm := by
  have hnb : ∀ v : Fin 11, (cycleGraph 11).neighborFinset v = {v - 1, v + 1} := by decide
  have hne : ∀ v : Fin 11, v - 1 ≠ v + 1 := by decide
  ext j l
  have hsum : ((cycleGraph 11).adjMatrix ℂ * Fm) j l = Fm (j - 1) l + Fm (j + 1) l := by
    rw [Matrix.mul_apply]
    simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, hnb j,
      Finset.sum_pair (hne j)]
  have hadd : (j + 1).val = (j.val + 1) % 11 := by simp [Fin.val_add]
  have hsub : (j - 1).val = (j.val + 10) % 11 := by
    simp only [Fin.sub_def]
    congr 1
    omega
  have h1 : Fm (j + 1) l = Fm j l * om ^ l.val := by
    simp only [Fm, hadd, om_pow_mod_mul]
    rw [← pow_add]
    congr 1
    ring
  have h2 : Fm (j - 1) l = Fm j l * om ^ (10 * l.val) := by
    simp only [Fm, hsub, om_pow_mod_mul]
    rw [← pow_add]
    congr 1
    ring
  rw [hsum, h1, h2, ← mul_add, add_comm (om ^ (10 * l.val)) (om ^ l.val), om_pow_add_om_pow,
    Dm, Matrix.mul_diagonal]

/-- **Hückel spectrum of the cycle `C₁₁`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph on 11 vertices splits as `∏ (X - 2 cos (2πk/11))`, `k = 0, …, 10`;
i.e. the adjacency eigenvalues of `C₁₁` are exactly `2 cos (2πk/11)`, with multiplicity. -/
theorem huckel_C11 :
    ((cycleGraph 11).adjMatrix ℂ).charpoly =
      ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ)) := by
  have hGF : Gm * Fm = 1 := mul_eq_one_comm.mp Fm_mul_Gm
  have hA : (cycleGraph 11).adjMatrix ℂ = Fm * (Dm * Gm) := by
    rw [← Matrix.mul_assoc, ← adjMatrix_mul_Fm, Matrix.mul_assoc, Fm_mul_Gm, Matrix.mul_one]
  rw [hA, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hGF, Matrix.mul_one]
  simpa [Dm] using Matrix.charpoly_diagonal
    (fun k : Fin 11 => ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ))

/-- **Hückel spectrum of the cycle `C₁₁`, as a set.**  The eigenvalues of the adjacency matrix
of `C₁₁` are exactly the numbers `2 cos (2πk/11)`, `k = 0, …, 10`. -/
theorem huckel_C11_spectrum :
    spectrum ℂ ((cycleGraph 11).adjMatrix ℂ) =
      Set.range fun k : Fin 11 => ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_range]
  exact exists_congr fun _ =>
    ⟨fun h => (sub_eq_zero.mp h).symm, fun h => by rw [h, sub_self]⟩

end Chem

