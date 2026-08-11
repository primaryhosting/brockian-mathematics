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

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/
def C13 : SimpleGraph (ZMod 13) := SimpleGraph.fromRel (fun i j => j = i + 1)

instance : DecidableRel C13.Adj := fun i j => by
  unfold C13 SimpleGraph.fromRel; infer_instance

/-- The adjacency matrix of the cycle graph `C₁₃`, with complex entries. -/
def adjC13 : Matrix (ZMod 13) (ZMod 13) ℂ := C13.adjMatrix ℂ

/-- A primitive 13th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (13 : ℕ))

/-- The standard additive character of `ZMod 13`. -/
noncomputable def ee (x : ZMod 13) : ℂ := zeta ^ x.val

lemma zeta_primitive : IsPrimitiveRoot zeta 13 :=
  Complex.isPrimitiveRoot_exp 13 (by norm_num)

lemma zeta_pow_13 : zeta ^ (13 : ℕ) = 1 := zeta_primitive.pow_eq_one

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 13) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 13]
  rw [pow_add, pow_mul, zeta_pow_13, one_pow, one_mul]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_add (x y : ZMod 13) : ee (x + y) = ee x * ee y := by
  simp only [ee, ZMod.val_add, zeta_pow_mod, pow_add]

lemma ee_neg (x : ZMod 13) : ee (-x) = (ee x)⁻¹ := by
  have h : ee x * ee (-x) = 1 := by rw [← ee_add]; simp [ee_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma ee_ne_zero (x : ZMod 13) : ee x ≠ 0 := by
  simp [ee, zeta, Complex.exp_ne_zero]

lemma ee_eq_exp (x : ZMod 13) :
    ee x = Complex.exp ((2 * Real.pi * (x.val : ℝ) / 13 : ℝ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ee k + ee (-k) = 2 cos (2πk/13)`. -/
lemma ee_add_ee_neg (x : ZMod 13) :
    ee x + ee (-x) = ((2 * Real.cos (2 * Real.pi * (x.val : ℝ) / 13) : ℝ) : ℂ) := by
  have key : ∀ t : ℂ, Complex.exp (t * Complex.I) + (Complex.exp (t * Complex.I))⁻¹
      = 2 * Complex.cos t := by
    intro t
    rw [← Complex.exp_neg, show -(t * Complex.I) = (-t) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [ee_neg, ee_eq_exp, key]
  push_cast [Complex.ofReal_cos]
  ring

lemma adj_iff (i j : ZMod 13) : C13.Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  have hne : ∀ a : ZMod 13, a ≠ a + 1 := by decide
  have hne' : ∀ a : ZMod 13, a ≠ a - 1 := by decide
  rw [C13, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h
    · exact Or.inr (by rw [h]; ring)
  · rintro (h | h) <;> subst h
    · exact ⟨hne i, Or.inl rfl⟩
    · exact ⟨hne' i, Or.inr (by ring)⟩

lemma neighborFinset_eq (i : ZMod 13) :
    C13.neighborFinset i = {i + 1, i - 1} := by
  ext j
  simp [SimpleGraph.mem_neighborFinset, adj_iff]

lemma mulVec_apply (v : ZMod 13 → ℂ) (i : ZMod 13) :
    adjC13.mulVec v i = v (i + 1) + v (i - 1) := by
  have hne : ∀ a : ZMod 13, (a + 1 : ZMod 13) ≠ a - 1 := by decide
  rw [adjC13, SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_eq, Finset.sum_pair (hne i)]

/-- The eigenvector attached to the frequency `k`. -/
noncomputable def evec (k : ZMod 13) : ZMod 13 → ℂ := fun i => ee (i * k)

/-- The eigenvalue attached to the frequency `k`. -/
noncomputable def eval13 (k : ZMod 13) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 13) : ℝ) : ℂ)

lemma mulVec_evec (k : ZMod 13) :
    adjC13.mulVec (evec k) = eval13 k • evec k := by
  funext i
  rw [mulVec_apply]
  have h1 : (i + 1) * k = i * k + k := by ring
  have h2 : (i - 1) * k = i * k + (-k) := by ring
  simp only [evec, h1, h2, ee_add, Pi.smul_apply, smul_eq_mul, eval13]
  rw [← ee_add_ee_neg k]
  ring

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def fmat : Matrix (ZMod 13) (ZMod 13) ℂ := fun i k => ee (i * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def gmat : Matrix (ZMod 13) (ZMod 13) ℂ := fun k j => (13 : ℂ)⁻¹ * ee (-(k * j))

lemma sum_ee : ∑ x : ZMod 13, ee x = 0 := by
  have h : (∑ x : ZMod 13, ee x) = ∑ m ∈ Finset.range 13, zeta ^ m :=
    Fin.sum_univ_eq_sum_range (fun m => zeta ^ m) 13
  rw [h, zeta_primitive.geom_sum_eq_zero (by norm_num)]

lemma sum_ee_mul (c : ZMod 13) :
    ∑ k : ZMod 13, ee (k * c) = if c = 0 then 13 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ee_zero]
  · rw [if_neg hc, ← sum_ee]
    exact Fintype.sum_equiv (Equiv.mulRight₀ c hc) _ _ (fun k => rfl)

lemma fmat_mul_gmat : fmat * gmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [fmat, gmat]
  have h : ∀ k : ZMod 13, ee (i * k) * ((13 : ℂ)⁻¹ * ee (-(k * j))) =
      (13 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    rw [show k * (i - j) = i * k + -(k * j) by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_ee_mul]
  by_cases hij : i = j
  · simp [hij, Matrix.one_apply]
  · have h0 : i - j ≠ 0 := sub_ne_zero.mpr hij
    simp [h0, hij]

lemma isUnit_fmat : IsUnit fmat := by
  have h2 : gmat * fmat = 1 := mul_eq_one_comm.mp fmat_mul_gmat
  exact ⟨⟨fmat, gmat, fmat_mul_gmat, h2⟩, rfl⟩

lemma adj_mul_fmat : adjC13 * fmat = fmat * Matrix.diagonal eval13 := by
  ext i k
  have h : (adjC13 * fmat) i k = adjC13.mulVec (evec k) i := rfl
  rw [h, mulVec_evec]
  simp [Matrix.mul_apply, Matrix.diagonal, evec, fmat, mul_comm]

lemma charpoly_eq_prod_zmod :
    adjC13.charpoly = ∏ k : ZMod 13, (X - C (eval13 k)) := by
  obtain ⟨u, hu⟩ := isUnit_fmat
  have key := adj_mul_fmat
  rw [← hu] at key
  have hA : adjC13
      = u.val * Matrix.diagonal eval13 * (u⁻¹ : (Matrix (ZMod 13) (ZMod 13) ℂ)ˣ).val := by
    calc adjC13 = adjC13 * (u.val * (u⁻¹ : (Matrix (ZMod 13) (ZMod 13) ℂ)ˣ).val) := by simp
      _ = (adjC13 * u.val) * (u⁻¹ : (Matrix (ZMod 13) (ZMod 13) ℂ)ˣ).val := by rw [mul_assoc]
      _ = _ := by rw [key]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel theory for the cycle `C₁₃`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₃` is `∏_{k=0}^{12} (X - 2 cos (2πk/13))`; i.e. the adjacency
eigenvalues of `C₁₃` are exactly the numbers `2 cos (2πk/13)`, `k = 0, …, 12`. -/
theorem huckel_C13 :
    adjC13.charpoly =
      ∏ k ∈ Finset.range 13,
        (X - C (((2 * Real.cos (2 * Real.pi * (k : ℝ) / 13) : ℝ) : ℂ))) := by
  rw [charpoly_eq_prod_zmod]
  exact Fin.prod_univ_eq_prod_range
    (fun m => (X - C (((2 * Real.cos (2 * Real.pi * (m : ℝ) / 13) : ℝ) : ℂ)))) 13

/-- Each of the 13 numbers `2 cos (2πk/13)` is an eigenvalue of the adjacency matrix
of `C₁₃`, with an explicit eigenvector. -/
theorem huckel_C13_eigenvector (k : ℕ) (hk : k < 13) :
    ∃ v : ZMod 13 → ℂ, v ≠ 0 ∧
      adjC13.mulVec v = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 13) : ℝ) : ℂ) • v := by
  refine ⟨evec (k : ZMod 13), ?_, ?_⟩
  · intro h
    have h0 : evec (k : ZMod 13) 0 = 0 := by rw [h]; rfl
    exact ee_ne_zero _ h0
  · have hval : ((k : ZMod 13)).val = k := ZMod.val_natCast_of_lt hk
    have := mulVec_evec (k : ZMod 13)
    rwa [eval13, hval] at this

/-- The spectrum of the adjacency matrix of `C₁₃` is the set of numbers `2 cos (2πk/13)`. -/
theorem huckel_C13_spectrum :
    spectrum ℂ adjC13 =
      (fun k : ℕ => (((2 * Real.cos (2 * Real.pi * (k : ℝ) / 13) : ℝ) : ℂ))) '' (Set.Iio 13) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C13]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_range, sub_eq_zero, Set.mem_image, Set.mem_Iio]
  exact ⟨fun ⟨k, hk, hz⟩ => ⟨k, hk, hz.symm⟩, fun ⟨k, hk, hz⟩ => ⟨k, hk, hz.symm⟩⟩

end Chem

