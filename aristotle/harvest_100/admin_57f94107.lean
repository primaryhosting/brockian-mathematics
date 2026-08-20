import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

/-- The character `Fin 14 → ℂ`, `x ↦ ω ^ x`. -/
noncomputable def chi (x : Fin 14) : ℂ := om ^ x.val

/-- The Fourier (DFT) matrix for `Fin 14`. -/
noncomputable def dft : Matrix (Fin 14) (Fin 14) ℂ := fun j k => chi (k * j)

/-- The Hückel eigenvalues of the cycle `C₁₄`. -/
noncomputable def hlam (k : Fin 14) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)

lemma om_primitive : IsPrimitiveRoot om 14 := by
  have := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [om, mul_comm, mul_assoc, mul_left_comm] using this

lemma om_pow_14 : om ^ 14 = 1 := om_primitive.pow_eq_one

lemma pow_mod_14 (z : ℂ) (hz : z ^ 14 = 1) (m : ℕ) : z ^ (m % 14) = z ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 14]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

lemma chi_add (a b : Fin 14) : chi (a + b) = chi a * chi b := by
  simp only [chi, Fin.val_add, pow_mod_14 om om_pow_14, pow_add]

lemma chi_zero : chi 0 = 1 := by simp [chi]

lemma chi_ne_zero (a : Fin 14) : chi a ≠ 0 := by
  simp [chi, om, Complex.exp_ne_zero]

lemma chi_sub (a b : Fin 14) : chi (a - b) = chi a * (chi b)⁻¹ := by
  have hab : a - b + b = a := sub_add_cancel a b
  have h : chi (a - b) * chi b = chi a := by rw [← chi_add, hab]
  rw [← h, mul_assoc, mul_inv_cancel₀ (chi_ne_zero b), mul_one]

lemma chi_mul (a b : Fin 14) : chi (a * b) = (chi a) ^ b.val := by
  simp only [chi, Fin.val_mul, pow_mod_14 om om_pow_14, pow_mul]

lemma chi_ne_one {m : Fin 14} (hm : m ≠ 0) : chi m ≠ 1 := by
  have h0 : m.val ≠ 0 := by
    intro h
    exact hm (by ext; simpa using h)
  exact om_primitive.pow_ne_one_of_pos_of_lt h0 m.isLt

lemma chi_pow_14 (m : Fin 14) : (chi m) ^ 14 = 1 := by
  rw [chi, ← pow_mul, mul_comm, pow_mul, om_pow_14, one_pow]

lemma chi_sum (m : Fin 14) : ∑ k : Fin 14, chi (k * m) = if m = 0 then 14 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [chi_zero]
  · have hstep : ∀ k : Fin 14, chi (k * m) = (chi m) ^ k.val := by
      intro k
      rw [mul_comm, chi_mul]
    rw [if_neg hm]
    calc ∑ k : Fin 14, chi (k * m) = ∑ k : Fin 14, (chi m) ^ (k : ℕ) :=
          Finset.sum_congr rfl fun k _ => hstep k
      _ = ∑ t ∈ Finset.range 14, (chi m) ^ t := (Finset.sum_range _).symm
      _ = 0 := by rw [geom_sum_eq (chi_ne_one hm), chi_pow_14, sub_self, zero_div]

lemma chi_eq_exp (k : Fin 14) :
    chi k = Complex.exp (((2 * Real.pi * (k : ℝ) / 14 : ℝ) : ℂ) * Complex.I) := by
  rw [chi, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma chi_add_inv (k : Fin 14) : chi k + (chi k)⁻¹ = hlam k := by
  have h1 : chi k = Complex.exp (((2 * Real.pi * (k : ℝ) / 14 : ℝ) : ℂ) * Complex.I) :=
    chi_eq_exp k
  have h2 : (chi k)⁻¹
      = Complex.exp (-(((2 * Real.pi * (k : ℝ) / 14 : ℝ) : ℂ) * Complex.I)) := by
    rw [h1, ← Complex.exp_neg]
  rw [h2, h1, hlam]
  push_cast
  rw [Complex.two_cos, neg_mul]

lemma cycle_adj_iff (j i : Fin 14) :
    (SimpleGraph.cycleGraph 14).Adj j i ↔ (i = j - 1 ∨ i = j + 1) := by
  revert j i
  decide

lemma adj_apply (j i : Fin 14) :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) j i = if i = j - 1 ∨ i = j + 1 then 1 else 0 := by
  rw [SimpleGraph.adjMatrix_apply]
  simp only [cycle_adj_iff]

lemma sub_one_ne_add_one (x : Fin 14) : x - 1 ≠ x + 1 := by
  revert x; decide

/-- The adjacency matrix is diagonalised by the DFT matrix: `A * F = F * D`. -/
lemma adj_mul_dft :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) * dft = dft * Matrix.diagonal hlam := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∀ i : Fin 14, ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) j i * dft i k
      = (if i = j - 1 then chi (k * i) else 0) + (if i = j + 1 then chi (k * i) else 0) := by
    intro i
    rw [adj_apply]
    rcases eq_or_ne i (j - 1) with h1 | h1
    · simp [h1, dft, sub_one_ne_add_one j]
    · rcases eq_or_ne i (j + 1) with h2 | h2
      · simp [h2, dft, Ne.symm (sub_one_ne_add_one j)]
      · simp [h1, h2, dft]
  rw [Finset.sum_congr rfl fun i _ => hL i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => chi (k * i)),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => chi (k * i))]
  simp only [Finset.mem_univ, if_true]
  have hR : ∑ i : Fin 14, dft j i * Matrix.diagonal hlam i k = chi (k * j) * hlam k := by
    rw [Finset.sum_eq_single k]
    · simp [dft]
    · intro b _ hb
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hR]
  have e1 : k * (j - 1) = k * j - k := by rw [mul_sub, mul_one]
  have e2 : k * (j + 1) = k * j + k := by rw [mul_add, mul_one]
  rw [e1, e2, chi_sub, chi_add, ← chi_add_inv k]
  ring

/-- The (normalised) inverse of the DFT matrix. -/
noncomputable def dftInv : Matrix (Fin 14) (Fin 14) ℂ := fun k i => (14 : ℂ)⁻¹ * (chi (k * i))⁻¹

lemma dft_mul_dftInv : dft * dftInv = 1 := by
  ext j i
  rw [Matrix.mul_apply]
  have hL : ∀ k : Fin 14, dft j k * dftInv k i = (14 : ℂ)⁻¹ * chi (k * (j - i)) := by
    intro k
    have h : k * (j - i) = k * j - k * i := mul_sub k j i
    rw [dft, dftInv, h, chi_sub]
    ring
  rw [Finset.sum_congr rfl fun k _ => hL k, ← Finset.mul_sum, chi_sum]
  by_cases h : j = i
  · subst h
    simp
  · have hji : j - i ≠ 0 := sub_ne_zero_of_ne h
    rw [if_neg hji]
    simp [h]

lemma isUnit_dft : IsUnit dft := IsUnit.of_mul_eq_one dftInv dft_mul_dftInv

/-- **Hückel theory for `C₁₄`**: the eigenvalues (spectrum) of the adjacency matrix of the
cycle graph `C₁₄` are exactly `2 cos (2πk/14)` for `k = 0, …, 13`. -/
theorem huckel_C14 :
    spectrum ℂ ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) =
      Set.range (fun k : Fin 14 => ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := isUnit_dft
  have hA : ((SimpleGraph.cycleGraph 14).adjMatrix ℂ)
      = (u : Matrix (Fin 14) (Fin 14) ℂ) * Matrix.diagonal hlam
        * ((u⁻¹ : (Matrix (Fin 14) (Fin 14) ℂ)ˣ) : Matrix (Fin 14) (Fin 14) ℂ) := by
    have h : ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) * (u : Matrix (Fin 14) (Fin 14) ℂ)
        = (u : Matrix (Fin 14) (Fin 14) ℂ) * Matrix.diagonal hlam := by
      rw [hu]; exact adj_mul_dft
    rw [← h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [hA, spectrum.units_conjugate, spectrum_diagonal]
  rfl

end Chem

