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

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

lemma zeta_primitive : IsPrimitiveRoot zeta 18 := by
  have := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  convert this using 2

lemma zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

/-- `ee m = ζ ^ m` for integer exponents. -/
noncomputable def ee (m : ℤ) : ℂ := zeta ^ m

lemma ee_add (a b : ℤ) : ee (a + b) = ee a * ee b := zpow_add₀ zeta_ne_zero a b

lemma ee_congr {a b : ℤ} (h : (18 : ℤ) ∣ a - b) : ee a = ee b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + 18 * t := by omega
  rw [hab, ee, zpow_add₀ zeta_ne_zero, _root_.zpow_mul,
    show ((zeta : ℂ) ^ (18 : ℤ)) = 1 by exact_mod_cast zeta_primitive.pow_eq_one]
  simp [ee]

lemma ee_ne_one {d : ℤ} (h : ¬ (18 : ℤ) ∣ d) : ee d ≠ 1 := by
  intro hc
  refine h ?_
  have hd := zeta_primitive.zpow_eq_one_iff_dvd d
  simp only [ee] at hc
  exact_mod_cast hd.mp hc

lemma ee_pow (k : ℕ) (d : ℤ) : ee ((k : ℤ) * d) = (ee d) ^ k := by
  rw [ee, ee, mul_comm, _root_.zpow_mul, zpow_natCast]

lemma ee_mul_congr {a b c : ℕ} (h : a % 18 = b % 18) : ee ((a : ℤ) * c) = ee ((b : ℤ) * c) := by
  apply ee_congr
  have h18 : (18 : ℤ) ∣ (a : ℤ) - b := by omega
  obtain ⟨t, ht⟩ := h18
  exact ⟨t * c, by linear_combination (c : ℤ) * ht⟩

lemma ee_cos (c : ℕ) :
    ee (c : ℤ) + ee (-(c : ℤ)) = 2 * ((Real.cos (2 * Real.pi * c / 18) : ℝ) : ℂ) := by
  have h1 : ee (c : ℤ) = Complex.exp (((2 * Real.pi * c / 18 : ℝ) : ℂ) * Complex.I) := by
    rw [ee, zpow_natCast, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : ee (-(c : ℤ)) = Complex.exp (-(((2 * Real.pi * c / 18 : ℝ) : ℂ) * Complex.I)) := by
    rw [ee, _root_.zpow_neg, zpow_natCast, zeta, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [h1, h2, Complex.exp_mul_I,
    show (-((((2 * Real.pi * c / 18 : ℝ)) : ℂ) * Complex.I))
        = ((-(2 * Real.pi * c / 18 : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

lemma ee_sum (d : ℤ) :
    (∑ k : Fin 18, ee ((k : ℕ) * d)) = if (18 : ℤ) ∣ d then 18 else 0 := by
  split_ifs with h
  · have h1 : ∀ k : Fin 18, ee ((k : ℕ) * d) = 1 := by
      intro k
      rw [ee_congr (b := 0) (by simpa using Dvd.dvd.mul_left h _), ee]
      simp
    simp [h1]
  · have hx : ee d ≠ 1 := ee_ne_one h
    have h18 : (ee d) ^ (18 : ℕ) = 1 := by
      rw [← ee_pow]
      exact (ee_congr (b := 0) (by simp)).trans (by simp [ee])
    have hsum : (∑ k : Fin 18, ee ((k : ℕ) * d)) = ∑ i ∈ Finset.range 18, (ee d) ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ee ((i : ℕ) * d))]
      exact Finset.sum_congr rfl fun i _ => ee_pow i d
    rw [hsum, geom_sum_eq hx, h18]
    simp

/-- The (unnormalized) discrete Fourier matrix of size 18. -/
noncomputable def F : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.of fun j k => ee ((j : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def G : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.of fun k m => (18 : ℂ)⁻¹ * ee (-((k : ℕ) * (m : ℕ)))

lemma dvd_sub_iff_eq {j m : Fin 18} : (18 : ℤ) ∣ ((j : ℕ) : ℤ) - ((m : ℕ) : ℤ) ↔ j = m := by
  constructor
  · intro hd
    have hj := j.isLt
    have hm := m.isLt
    omega
  · rintro rfl
    simp

lemma F_mul_G : F * G = 1 := by
  ext j m
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 18,
      F j k * G k m = (18 : ℂ)⁻¹ * ee ((k : ℕ) * (((j : ℕ) : ℤ) - ((m : ℕ) : ℤ))) := by
    intro k
    simp only [F, G, Matrix.of_apply]
    rw [show ((k : ℕ) : ℤ) * (((j : ℕ) : ℤ) - ((m : ℕ) : ℤ))
          = ((j : ℕ) : ℤ) * ((k : ℕ) : ℤ) + (-(((k : ℕ) : ℤ) * ((m : ℕ) : ℤ))) by ring, ee_add]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, ee_sum]
  rcases eq_or_ne j m with h | h
  · subst h; simp
  · rw [if_neg (fun hd => h (dvd_sub_iff_eq.mp hd)), Matrix.one_apply_ne h, mul_zero]

lemma G_mul_F : G * F = 1 := by
  ext j m
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 18,
      G j k * F k m = (18 : ℂ)⁻¹ * ee ((k : ℕ) * (((m : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
    intro k
    simp only [F, G, Matrix.of_apply]
    rw [show ((k : ℕ) : ℤ) * (((m : ℕ) : ℤ) - ((j : ℕ) : ℤ))
          = (-(((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) + ((k : ℕ) : ℤ) * ((m : ℕ) : ℤ) by ring, ee_add]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, ee_sum]
  rcases eq_or_ne j m with h | h
  · subst h; simp
  · rw [if_neg (fun hd => h (dvd_sub_iff_eq.mp hd).symm), Matrix.one_apply_ne h, mul_zero]

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/18)`. -/
noncomputable def D : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.diagonal fun k => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℝ) : ℂ)

lemma fin18_sub_one_ne_add_one : ∀ i : Fin 18, (i - 1 : Fin 18) ≠ i + 1 := by decide

lemma fin18_sub_one : ∀ i : Fin 18, (i - 1 : Fin 18) = i + 17 := by decide

lemma adj_mul_F : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) * F = F * D := by
  ext i k
  have hL : (((SimpleGraph.cycleGraph 18).adjMatrix ℂ) * F) i k = F (i - 1) k + F (i + 1) k := by
    show (((SimpleGraph.cycleGraph 18).adjMatrix ℂ) *ᵥ (fun j => F j k)) i = _
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset (n := 16),
      Finset.sum_pair (fin18_sub_one_ne_add_one i)]
  rw [hL, D, Matrix.mul_diagonal]
  simp only [F, Matrix.of_apply, fin18_sub_one]
  have e1 : ee (((i + 17 : Fin 18) : ℕ) * (k : ℕ)) = ee (((((i : ℕ) + 17 : ℕ)) : ℤ) * (k : ℕ)) := by
    apply ee_mul_congr; simp [Fin.val_add]
  have e2 : ee (((i + 1 : Fin 18) : ℕ) * (k : ℕ)) = ee (((((i : ℕ) + 1 : ℕ)) : ℤ) * (k : ℕ)) := by
    apply ee_mul_congr; simp [Fin.val_add]
  rw [e1, e2]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have E1 : ee (((((i : ℕ) : ℤ)) + 17) * ((k : ℕ) : ℤ))
      = ee (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) * ee (-((k : ℕ) : ℤ)) := by
    rw [show (((((i : ℕ) : ℤ)) + 17) * ((k : ℕ) : ℤ))
          = ((i : ℕ) : ℤ) * ((k : ℕ) : ℤ) + 17 * ((k : ℕ) : ℤ) by ring, ee_add]
    congr 1
    exact ee_congr ⟨(k : ℕ), by ring⟩
  have E2 : ee (((((i : ℕ) : ℤ)) + 1) * ((k : ℕ) : ℤ))
      = ee (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) * ee (((k : ℕ) : ℤ)) := by
    rw [show (((((i : ℕ) : ℤ)) + 1) * ((k : ℕ) : ℤ))
          = ((i : ℕ) : ℤ) * ((k : ℕ) : ℤ) + ((k : ℕ) : ℤ) by ring, ee_add]
  rw [E1, E2, ← mul_add, add_comm (ee (-((k : ℕ) : ℤ))) (ee ((k : ℕ) : ℤ)), ee_cos]
  push_cast
  ring

/-- **Hückel theory for the C₁₈ annulene ring.**  The characteristic polynomial of the
adjacency matrix of the cycle graph `C₁₈` factors as `∏ k, (X - 2 cos (2πk/18))`, i.e. the
adjacency eigenvalues of `C₁₈` are exactly `2 cos (2πk/18)` for `k = 0, …, 17`. -/
theorem huckel_C18 :
    ((SimpleGraph.cycleGraph 18).adjMatrix ℂ).charpoly =
      ∏ k : Fin 18, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℝ) : ℂ)) := by
  have hU : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) = F * D * G := by
    rw [← adj_mul_F, Matrix.mul_assoc, F_mul_G, Matrix.mul_one]
  let U : (Matrix (Fin 18) (Fin 18) ℂ)ˣ := ⟨F, G, F_mul_G, G_mul_F⟩
  have : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) = U.val * D * (U⁻¹).val := hU
  rw [this, Matrix.charpoly_units_conj, D, Matrix.charpoly_diagonal]

/-- Restatement of `Chem.huckel_C18` in terms of the spectrum: the set of adjacency eigenvalues
of the cycle graph `C₁₈` is exactly `{2 cos (2πk/18) | k = 0, …, 17}`. -/
theorem huckel_C18_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : Fin 18, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℝ) : ℂ)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C18]
  simp [Polynomial.eval_prod, Polynomial.IsRoot, Finset.prod_eq_zero_iff, sub_eq_zero]

end Chem

