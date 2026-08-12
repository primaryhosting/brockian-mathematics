import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace Chem

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (10 : ℕ))

lemma zeta_primitive : IsPrimitiveRoot zeta 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

lemma zeta_pow_ten : zeta ^ 10 = 1 := zeta_primitive.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := by
  simp [zeta, Complex.exp_ne_zero]

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 10) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 10]
  rw [pow_add, pow_mul, zeta_pow_ten, one_pow, one_mul]

/-! ### The character `E` of `Fin 10` -/

/-- `E x = ζ ^ x`, a group homomorphism from `(Fin 10, +)` to `ℂˣ`. -/
noncomputable def E (x : Fin 10) : ℂ := zeta ^ (x : ℕ)

lemma E_add (x y : Fin 10) : E (x + y) = E x * E y := by
  simp only [E, Fin.val_add, zeta_pow_mod, pow_add]

lemma E_zero : E 0 = 1 := by simp [E]

lemma E_ne_zero (x : Fin 10) : E x ≠ 0 := pow_ne_zero _ zeta_ne_zero

lemma E_mul_neg (x : Fin 10) : E x * E (-x) = 1 := by
  rw [← E_add]; simp [E_zero]

lemma E_neg (x : Fin 10) : E (-x) = (E x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact E_mul_neg x)

lemma E_mul (x y : Fin 10) : E (x * y) = (E x) ^ (y : ℕ) := by
  simp only [E, Fin.val_mul, zeta_pow_mod, pow_mul]

lemma E_eq_one_iff (d : Fin 10) : E d = 1 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    have hd0 : (d : ℕ) ≠ 0 := by
      simpa [Fin.val_eq_zero_iff] using hd
    exact zeta_primitive.pow_ne_one_of_pos_of_lt hd0 d.isLt h
  · rintro rfl; exact E_zero

lemma E_sum (d : Fin 10) : ∑ k : Fin 10, E (d * k) = if d = 0 then 10 else 0 := by
  have h : ∀ k : Fin 10, E (d * k) = (E d) ^ (k : ℕ) := fun k => E_mul d k
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => (E d) ^ i) 10]
  by_cases hd : d = 0
  · subst hd
    simp [E_zero]
  · have h1 : E d ≠ 1 := fun hc => hd ((E_eq_one_iff d).mp hc)
    have h10 : (E d) ^ 10 = 1 := by
      rw [E, ← pow_mul, mul_comm, pow_mul, zeta_pow_ten, one_pow]
    rw [geom_sum_eq h1, h10, sub_self, zero_div, if_neg hd]

/-! ### The matrices -/

/-- Adjacency matrix of the cycle graph `C₁₀`. -/
noncomputable def Am : Matrix (Fin 10) (Fin 10) ℂ :=
  (SimpleGraph.cycleGraph 10).adjMatrix ℂ

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def Pm : Matrix (Fin 10) (Fin 10) ℂ := fun j k => E (j * k)

/-- The inverse Fourier matrix. -/
noncomputable def Qm : Matrix (Fin 10) (Fin 10) ℂ := fun k l => (10 : ℂ)⁻¹ * E (-(k * l))

/-- The eigenvalues, as a function on `Fin 10`. -/
noncomputable def Dv : Fin 10 → ℂ := fun l => E l + E (-l)

lemma Pm_mul_Qm : Pm * Qm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have : ∀ k : Fin 10, Pm j k * Qm k l = (10 : ℂ)⁻¹ * E ((j - l) * k) := by
    intro k
    simp only [Pm, Qm]
    rw [← mul_assoc, mul_comm (E (j * k)) ((10:ℂ)⁻¹), mul_assoc, ← E_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, E_sum]
  by_cases h : j = l
  · subst h
    simp
  · have : j - l ≠ 0 := sub_ne_zero_of_ne h
    simp [this, h]

lemma Qm_mul_Pm : Qm * Pm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have : ∀ k : Fin 10, Qm j k * Pm k l = (10 : ℂ)⁻¹ * E ((l - j) * k) := by
    intro k
    simp only [Pm, Qm]
    rw [mul_assoc, ← E_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, E_sum]
  by_cases h : j = l
  · subst h
    simp
  · have : l - j ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
    simp [this, h]

lemma Am_apply (j k : Fin 10) :
    Am j k = (if k = j - 1 then (1 : ℂ) else 0) + (if k = j + 1 then (1 : ℂ) else 0) := by
  have hadj : (SimpleGraph.cycleGraph 10).Adj j k ↔ (k = j - 1 ∨ k = j + 1) := by
    rw [SimpleGraph.cycleGraph_adj]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (rfl | rfl)
      · left; ring
      · right; ring
  have hne : (j - 1 : Fin 10) ≠ j + 1 := by
    intro h
    have h2 : (2 : Fin 10) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  simp only [Am, SimpleGraph.adjMatrix_apply, hadj]
  by_cases h1 : k = j - 1
  · simp [h1, hne]
  · by_cases h2 : k = j + 1 <;> simp [h1, h2, Ne.symm hne]

lemma Am_mul_Pm : Am * Pm = Pm * Matrix.diagonal Dv := by
  ext j l
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have : ∀ k : Fin 10, Am j k * Pm k l =
      (if k = j - 1 then E (k * l) else 0) + (if k = j + 1 then E (k * l) else 0) := by
    intro k
    rw [Am_apply]
    simp only [Pm]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun k => E (k * l)),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun k => E (k * l))]
  simp only [Finset.mem_univ, if_true]
  simp only [Pm, Dv]
  have e1 : ((j - 1) * l : Fin 10) = j * l + (-l) := by ring
  have e2 : ((j + 1) * l : Fin 10) = j * l + l := by ring
  rw [e1, e2, E_add, E_add]
  ring

lemma Am_eq_conj : Am = Pm * Matrix.diagonal Dv * Qm := by
  rw [← Am_mul_Pm, Matrix.mul_assoc, Pm_mul_Qm, Matrix.mul_one]

/-- The Fourier matrix as a unit of the matrix ring. -/
noncomputable def Um : (Matrix (Fin 10) (Fin 10) ℂ)ˣ :=
  ⟨Pm, Qm, Pm_mul_Qm, Qm_mul_Pm⟩

lemma charpoly_Am : Am.charpoly = ∏ l : Fin 10, (Polynomial.X - Polynomial.C (Dv l)) := by
  have hU : (Um : Matrix (Fin 10) (Fin 10) ℂ) = Pm := rfl
  have hUinv : ((Um⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) : Matrix (Fin 10) (Fin 10) ℂ) = Qm := rfl
  have := Matrix.charpoly_units_conj Um (Matrix.diagonal Dv)
  rw [hU, hUinv] at this
  rw [Am_eq_conj, this, Matrix.charpoly_diagonal]

lemma Dv_eq (l : Fin 10) :
    Dv l = ((2 * Real.cos (2 * Real.pi * (l : ℕ) / 10) : ℝ) : ℂ) := by
  have hE : E l = Complex.exp ((2 * Real.pi * (l : ℕ) / 10 : ℝ) * Complex.I) := by
    rw [E, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hEn : E (-l) = Complex.exp (-((2 * Real.pi * (l : ℕ) / 10 : ℝ) * Complex.I)) := by
    rw [E_neg, hE, ← Complex.exp_neg]
  rw [Dv, hE, hEn]
  push_cast
  rw [Complex.two_cos]
  ring_nf

/-- **Hückel theory for the cycle `C₁₀`**: the characteristic polynomial of the adjacency
matrix of the cycle graph on 10 vertices factors as `∏ (X - 2cos(2πk/10))`, i.e. the
adjacency eigenvalues of `C₁₀` are exactly `2 cos(2πk/10)` for `k = 0, …, 9`. -/
theorem huckel_C10 :
    ((SimpleGraph.cycleGraph 10).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 10,
        (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 10) : ℝ) : ℂ)) := by
  have h := charpoly_Am
  rw [Am] at h
  rw [h]
  rw [Finset.prod_congr rfl (fun l _ => by rw [Dv_eq l])]
  exact Fin.prod_univ_eq_prod_range
    (fun i => Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * i / 10) : ℝ) : ℂ)) 10

/-- Consequence of `Chem.huckel_C10`: a complex number `μ` is an eigenvalue of the adjacency
matrix of `C₁₀` (i.e. it admits a nonzero eigenvector) exactly when `μ = 2 cos (2πk/10)` for
some `k < 10`. -/
theorem huckel_C10_eigenvalue_iff (mu : ℂ) :
    (∃ v : Fin 10 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 10).adjMatrix ℂ *ᵥ v = mu • v) ↔
      ∃ k : ℕ, k < 10 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 10) : ℝ) : ℂ) := by
  have hsc : ∀ v : Fin 10 → ℂ, (Matrix.scalar (Fin 10) mu) *ᵥ v = mu • v := by
    intro v
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have key : (∃ v : Fin 10 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 10).adjMatrix ℂ *ᵥ v = mu • v) ↔
      (Matrix.scalar (Fin 10) mu - (SimpleGraph.cycleGraph 10).adjMatrix ℂ).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, hsc, sub_self]⟩
    · rintro ⟨v, hv, h⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at h
      exact h.symm
  rw [key, ← Matrix.eval_charpoly, huckel_C10, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mp hk, sub_eq_zero.mp h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mpr hk, sub_eq_zero.mpr h⟩

end Chem

