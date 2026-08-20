/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma zeta_primitive : IsPrimitiveRoot zeta 17 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 17 (by norm_num)

lemma zeta_pow_17 : zeta ^ 17 = 1 := zeta_primitive.pow_eq_one

lemma zeta_ne_one : zeta ≠ 1 := by
  simpa using zeta_primitive.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num)

/-- The standard additive character of `ZMod 17`, `x ↦ exp (2πi x / 17)`. -/
noncomputable def ee (x : ZMod 17) : ℂ := zeta ^ x.val

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 17) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 17]
  rw [pow_add, pow_mul, zeta_pow_17, one_pow, one_mul]

lemma ee_add (x y : ZMod 17) : ee (x + y) = ee x * ee y := by
  simp only [ee, ZMod.val_add, zeta_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (x : ZMod 17) : ee x ≠ 0 := by
  simp [ee, zeta, Complex.exp_ne_zero]

lemma ee_neg (x : ZMod 17) : ee (-x) = (ee x)⁻¹ := by
  have h : ee x * ee (-x) = 1 := by rw [← ee_add]; simp [ee_zero]
  field_simp [ee_ne_zero]
  linear_combination h

lemma ee_eq_exp (k : ZMod 17) :
    ee k = Complex.exp (((2 * Real.pi * k.val / 17 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma sum_ee : ∑ x : ZMod 17, ee x = 0 := by
  have h : ∑ x : ZMod 17, ee x = ∑ n ∈ Finset.range 17, zeta ^ n := by
    rw [Finset.sum_nbij' (i := fun (x : ZMod 17) => x.val) (j := fun (n : ℕ) => (n : ZMod 17))] <;>
      simp [ZMod.val_lt, ee]
  rw [h, geom_sum_eq zeta_ne_one, zeta_pow_17]
  simp

lemma sum_ee_mul (t : ZMod 17) : ∑ m : ZMod 17, ee (m * t) = if t = 0 then 17 else 0 := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  by_cases ht : t = 0
  · subst ht; simp [ee_zero]
  · rw [if_neg ht]
    rw [Fintype.sum_equiv (Equiv.mulRight₀ t ht) (fun m => ee (m * t)) ee (fun m => rfl)]
    exact sum_ee

/-! ### The adjacency matrix of `C₁₇` -/

/-- The adjacency matrix of the cycle graph `C₁₇`, with vertices indexed by `ZMod 17`:
two vertices are adjacent exactly when they differ by `1` modulo `17`. -/
def C17adj : Matrix (ZMod 17) (ZMod 17) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The adjacency matrix is symmetric. -/
lemma C17adj_transpose : C17adj.transpose = C17adj := by
  funext i j
  simp only [Matrix.transpose_apply, C17adj, Matrix.of_apply]
  congr 1
  exact propext (or_comm)

/-- Every vertex of `C₁₇` has exactly two neighbours, so `C17adj` really is the adjacency
matrix of a `17`-cycle. -/
lemma C17adj_degree (i : ZMod 17) :
    (Finset.univ.filter (fun j : ZMod 17 => i - j = 1 ∨ j - i = 1)).card = 2 := by
  revert i
  decide

lemma mulVec_C17adj (v : ZMod 17 → ℂ) (i : ZMod 17) :
    (C17adj *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hlt : ∀ j : ZMod 17, (i - j = 1) ↔ (j = i - 1) := by
    intro j
    constructor
    · intro h; rw [← h]; ring
    · intro h; subst h; ring
  have hgt : ∀ j : ZMod 17, (j - i = 1) ↔ (j = i + 1) := by
    intro j
    constructor
    · intro h; rw [← h]; ring
    · intro h; subst h; ring
  have key : ∀ j : ZMod 17, C17adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    simp only [C17adj, Matrix.of_apply, hlt, hgt]
    by_cases h1 : j = i - 1
    · subst h1; simp [hne]
    · by_cases h2 : j = i + 1
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp only [Matrix.mulVec, dotProduct, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-! ### The Hückel eigenvalues -/

/-- The `k`-th Hückel eigenvalue of `C₁₇`: `2 cos (2πk/17)`. -/
noncomputable def lam (k : ZMod 17) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 17)

lemma exp_add_inv (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹
      = 2 * Complex.cos (θ : ℂ) := by
  rw [← Complex.exp_neg, Complex.cos]
  ring_nf

lemma ee_add_ee_neg (k : ZMod 17) : ee k + ee (-k) = lam k := by
  rw [ee_neg, ee_eq_exp, exp_add_inv, lam, Complex.ofReal_cos]

/-- The Fourier vector `j ↦ exp (2πi k j / 17)` is an eigenvector of the adjacency matrix
of `C₁₇` with eigenvalue `2 cos (2πk/17)`. -/
lemma hasEigenvector (k : ZMod 17) :
    C17adj *ᵥ (fun j => ee (k * j)) = lam k • (fun j => ee (k * j)) := by
  funext i
  rw [mulVec_C17adj]
  have h1 : k * (i - 1) = k * i + -k := by ring
  have h2 : k * (i + 1) = k * i + k := by ring
  rw [h1, h2, ee_add, ee_add]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ee_add_ee_neg k]
  ring

lemma sum_shift (F : ZMod 17 → ℂ) : ∑ j : ZMod 17, F (j + 1) = ∑ j : ZMod 17, F j :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

/-- Fourier coefficients of a vector. -/
noncomputable def coeff (v : ZMod 17 → ℂ) (m : ZMod 17) : ℂ := ∑ j : ZMod 17, ee (-(m * j)) * v j

lemma coeff_eigen {v : ZMod 17 → ℂ} {μ : ℂ} (hv : C17adj *ᵥ v = μ • v) (m : ZMod 17) :
    μ * coeff v m = lam m * coeff v m := by
  have hstep : ∀ j : ZMod 17, μ * v j = v (j - 1) + v (j + 1) := by
    intro j
    have := congrFun hv j
    rw [mulVec_C17adj] at this
    simpa [mul_comm] using this.symm
  have hL : μ * coeff v m = ∑ j : ZMod 17, ee (-(m * j)) * (v (j - 1) + v (j + 1)) := by
    rw [coeff, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hstep j]; ring
  have hA : ∑ j : ZMod 17, ee (-(m * j)) * v (j - 1)
      = ∑ j : ZMod 17, (ee (-(m * j)) * ee (-m)) * v j := by
    rw [← sum_shift (fun j => ee (-(m * j)) * v (j - 1))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have harg : -(m * (j + 1)) = -(m * j) + -m := by ring
    rw [harg, ee_add]
    congr 2
    ring
  have hB : ∑ j : ZMod 17, ee (-(m * j)) * v (j + 1)
      = ∑ j : ZMod 17, (ee (-(m * j)) * ee m) * v j := by
    rw [← sum_shift (fun j => (ee (-(m * j)) * ee m) * v j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have harg : -(m * (j + 1)) + m = -(m * j) := by ring
    rw [← harg, ee_add]
  rw [hL]
  simp only [mul_add]
  rw [Finset.sum_add_distrib, hA, hB, coeff, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← ee_add_ee_neg m]
  ring

lemma inversion (v : ZMod 17 → ℂ) (i : ZMod 17) :
    ∑ m : ZMod 17, ee (m * i) * coeff v m = 17 * v i := by
  have h1 : ∑ m : ZMod 17, ee (m * i) * coeff v m
      = ∑ j : ZMod 17, (∑ m : ZMod 17, ee (m * (i - j))) * v j := by
    simp only [coeff, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun m _ => ?_))
    have harg : m * (i - j) = m * i + -(m * j) := by ring
    rw [harg, ee_add]
    ring
  rw [h1]
  have h2 : ∀ j : ZMod 17, (∑ m : ZMod 17, ee (m * (i - j))) * v j
      = if j = i then 17 * v i else 0 := by
    intro j
    rw [sum_ee_mul]
    by_cases hj : j = i
    · subst hj; simp
    · have : i - j ≠ 0 := fun h => hj (by rw [← sub_eq_zero]; rw [← neg_eq_zero]; rw [← h]; ring)
      simp [this, hj]
  rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_ite_eq']
  simp

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₁₇`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₇` if and only if `μ = 2 cos (2πk/17)` for some
`k ∈ {0, 1, …, 16}`. -/
theorem huckel_C17 (μ : ℂ) :
    (∃ v : ZMod 17 → ℂ, v ≠ 0 ∧ C17adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 17, μ = 2 * Real.cos (2 * Real.pi * k / 17) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hex : ∃ m : ZMod 17, coeff v m ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hv0
      funext i
      have := inversion v i
      rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by rw [hc m, mul_zero])] at this
      simp only [Finset.sum_const_zero] at this
      field_simp at this
      simpa using this
    obtain ⟨m, hm⟩ := hex
    have : μ = lam m := by
      have := coeff_eigen hv m
      exact mul_right_cancel₀ hm this
    refine ⟨⟨m.val, m.val_lt⟩, ?_⟩
    rw [this, lam]
  · rintro ⟨k, hk⟩
    set m : ZMod 17 := (k.val : ZMod 17)
    have hmval : m.val = k.val := ZMod.val_cast_of_lt k.isLt
    have hlam : μ = lam m := by rw [hk, lam, hmval]
    refine ⟨fun j => ee (m * j), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [ee_zero] at this
    · rw [hlam]
      exact hasEigenvector m

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

