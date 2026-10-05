import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (20 : ℕ))

lemma zeta_primitive : IsPrimitiveRoot zeta 20 :=
  Complex.isPrimitiveRoot_exp 20 (by norm_num)

lemma zeta_pow_twenty : zeta ^ 20 = 1 := zeta_primitive.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 20) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 20]
  rw [pow_add, pow_mul, zeta_pow_twenty, one_pow, one_mul]

/-- The character `k ↦ ζ^k` on `Fin 20` (viewed as `ZMod 20`). -/
noncomputable def ee (x : Fin 20) : ℂ := zeta ^ (x : ℕ)

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (x : Fin 20) : ee x ≠ 0 := pow_ne_zero _ zeta_ne_zero

lemma ee_add (x y : Fin 20) : ee (x + y) = ee x * ee y := by
  simp only [ee, Fin.val_add, zeta_pow_mod, pow_add]

lemma ee_sub (x y : Fin 20) : ee (x - y) = ee x * (ee y)⁻¹ := by
  have h : ee (x - y) * ee y = ee x := by rw [← ee_add, sub_add_cancel]
  exact (eq_mul_inv_iff_mul_eq₀ (ee_ne_zero y)).mpr h

lemma ee_mul_pow (m k : Fin 20) : ee (m * k) = (ee m) ^ (k : ℕ) := by
  simp only [ee, Fin.val_mul, zeta_pow_mod, pow_mul]

lemma ee_eq_one_iff (m : Fin 20) : ee m = 1 ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    have h0 : (m : ℕ) ≠ 0 := by
      intro hh
      exact hm (Fin.val_eq_zero_iff.mp hh)
    exact zeta_primitive.pow_ne_one_of_pos_of_lt h0 m.isLt h
  · rintro rfl; exact ee_zero

lemma ee_pow_twenty (m : Fin 20) : (ee m) ^ 20 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_twenty, one_pow]

lemma sum_ee (m : Fin 20) : (∑ k : Fin 20, ee (m * k)) = if m = 0 then 20 else 0 := by
  have h1 : (∑ k : Fin 20, ee (m * k)) = ∑ j ∈ Finset.range 20, (ee m) ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (ee m) ^ j) 20]
    exact Finset.sum_congr rfl (fun k _ => ee_mul_pow m k)
  rw [h1]
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero]
  · rw [if_neg hm]
    have hne : ee m ≠ 1 := fun h => hm ((ee_eq_one_iff m).mp h)
    rw [geom_sum_eq hne, ee_pow_twenty, sub_self, zero_div]

/-- The DFT matrix. -/
noncomputable def Pm : Matrix (Fin 20) (Fin 20) ℂ := Matrix.of fun i k => ee (i * k)

/-- The inverse DFT matrix. -/
noncomputable def Qm : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.of fun k j => (20 : ℂ)⁻¹ * (ee (j * k))⁻¹

/-- The diagonal matrix of eigenvalues. -/
noncomputable def Dm : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.diagonal (fun k => ee k + (ee k)⁻¹)

lemma Pm_mul_Qm : Pm * Qm = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 20, Pm i k * Qm k l = (20 : ℂ)⁻¹ * ee ((i - l) * k) := by
    intro k
    simp only [Pm, Qm, Matrix.of_apply]
    rw [sub_mul, ee_sub]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_ee]
  by_cases h : i = l
  · subst h
    rw [if_pos (sub_self i), Matrix.one_apply_eq]
    norm_num
  · rw [if_neg (fun hc => h (sub_eq_zero.mp hc)), Matrix.one_apply_ne h, mul_zero]

lemma adj_iff (i j : Fin 20) :
    (SimpleGraph.cycleGraph 20).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
  revert i j
  decide +kernel

lemma sub_one_ne_add_one (i : Fin 20) : i - 1 ≠ i + 1 := by
  revert i
  decide

lemma adj_mul_Pm : (SimpleGraph.cycleGraph 20).adjMatrix ℂ * Pm = Pm * Dm := by
  ext i k
  rw [Matrix.mul_apply, Dm, Matrix.mul_diagonal]
  have hterm : ∀ j : Fin 20, ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) i j * Pm j k
      = if j ∈ ({i - 1, i + 1} : Finset (Fin 20)) then Pm j k else 0 := by
    intro j
    simp only [SimpleGraph.adjMatrix_apply, Finset.mem_insert, Finset.mem_singleton, adj_iff]
    split <;> simp_all
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair (sub_one_ne_add_one i)]
  simp only [Pm, Matrix.of_apply]
  rw [show (i - 1) * k = i * k - k by rw [sub_mul, one_mul],
    show (i + 1) * k = i * k + k by rw [add_mul, one_mul],
    ee_sub, ee_add]
  ring

lemma ee_eq_exp (k : Fin 20) :
    ee k = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ee_add_inv (k : Fin 20) :
    ee k + (ee k)⁻¹ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) := by
  have h := ee_eq_exp k
  set t : ℂ := ((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) with ht
  rw [h, ← Complex.exp_neg, ← neg_mul]
  have : Complex.exp (t * Complex.I) + Complex.exp (-t * Complex.I) = 2 * Complex.cos t := by
    rw [Complex.cos]
    field_simp
  rw [this, ht, ← Complex.ofReal_cos]
  push_cast
  ring

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₂₀`
(the Hückel matrix of the annulene C₂₀ with `α = 0`, `β = 1`) factors as
`∏_{k=0}^{19} (X - 2cos(2πk/20))`. -/
theorem huckel_C20_charpoly :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 20,
        (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)) := by
  have hQP : Qm * Pm = 1 := mul_eq_one_comm.mp Pm_mul_Qm
  let U : (Matrix (Fin 20) (Fin 20) ℂ)ˣ := ⟨Pm, Qm, Pm_mul_Qm, hQP⟩
  have hA : (SimpleGraph.cycleGraph 20).adjMatrix ℂ
      = (U : Matrix (Fin 20) (Fin 20) ℂ) * Dm * ((U⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) :
        Matrix (Fin 20) (Fin 20) ℂ) := by
    show _ = Pm * Dm * Qm
    rw [← adj_mul_Pm, mul_assoc, Pm_mul_Qm, mul_one]
  rw [hA, Matrix.charpoly_units_conj, Dm, Matrix.charpoly_diagonal,
    ← Fin.prod_univ_eq_prod_range
      (fun k => Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)) 20]
  exact Finset.prod_congr rfl (fun k _ => by rw [ee_add_inv])

/-- **Hückel theory for C₂₀.** The eigenvalues of the adjacency matrix of the cycle graph
`C₂₀` are exactly the numbers `2 cos (2πk/20)` for `k = 0, …, 19`. -/
theorem huckel_C20 :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : ℕ, k < 20 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C20_charpoly]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Set.mem_setOf_eq]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mp hk, sub_eq_zero.mp h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mpr hk, by rw [h]; ring⟩

end Chem

