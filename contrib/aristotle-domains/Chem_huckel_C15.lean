/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Statement: The adjacency eigenvalues of the cycle graph C_15 are 2·cos(2πk/15) for k=0..14.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Complex

/-- The cyclic shift permutation matrix on `Fin 15`: `shift i j = 1` iff `i - 1 = j`. -/
def shift : Matrix (Fin 15) (Fin 15) ℂ :=
  (1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix (fun i => i - 1) id

lemma shift_apply (i j : Fin 15) : shift i j = if i - 1 = j then 1 else 0 := by
  simp [shift, Matrix.one_apply]

lemma submatrix_one_mul (f g : Fin 15 → Fin 15) :
    ((1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix f id) *
        ((1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix g id)
      = (1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix (g ∘ f) id := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id, Function.comp_apply]
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

private lemma ofNat_succ (m : ℕ) : Fin.ofNat 15 (m + 1) = Fin.ofNat 15 m + 1 := by
  ext; simp [Fin.ofNat, Fin.add_def]

lemma shift_pow (m : ℕ) :
    shift ^ m = (1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix (fun i => i - Fin.ofNat 15 m) id := by
  induction m with
  | zero =>
      have h : (fun i : Fin 15 => i - Fin.ofNat 15 0) = id := by
        funext i; show i - 0 = i; simp
      rw [pow_zero, h, Matrix.submatrix_id_id]
  | succ m ih =>
      rw [pow_succ, ih, shift, submatrix_one_mul]
      congr 1
      funext i
      simp only [Function.comp_apply, ofNat_succ]
      abel

lemma shift_pow_apply (m : ℕ) (i j : Fin 15) :
    (shift ^ m) i j = if i - Fin.ofNat 15 m = j then 1 else 0 := by
  rw [shift_pow]; simp [Matrix.one_apply]

lemma shift_pow_fifteen : shift ^ 15 = 1 := by
  have h : (fun i : Fin 15 => i - Fin.ofNat 15 15) = id := by
    funext i; show i - 0 = i; simp
  rw [shift_pow, h, Matrix.submatrix_id_id]

/-- The adjacency matrix of `C₁₅` is `S + S¹⁴ = S + S⁻¹` for the cyclic shift `S`. -/
lemma adjMatrix_eq : (SimpleGraph.cycleGraph 15).adjMatrix ℂ = shift + shift ^ 14 := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply, Matrix.add_apply, shift_apply, shift_pow_apply]
  have h14 : Fin.ofNat 15 14 = 14 := rfl
  rw [h14]
  simp only [SimpleGraph.cycleGraph_adj]
  by_cases h1 : i - 1 = j <;> by_cases h2 : i - 14 = j <;> simp [h1, h2] <;> omega

lemma shift_mulVec (v : Fin 15 → ℂ) (i : Fin 15) : (shift *ᵥ v) i = v (i - 1) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i - 1)]
  · simp [shift_apply]
  · intro b _ hb; simp [shift_apply, Ne.symm hb]
  · simp

lemma smul_one_mulVec (c : ℂ) (v : Fin 15 → ℂ) (i : Fin 15) :
    ((c • (1 : Matrix (Fin 15) (Fin 15) ℂ)) *ᵥ v) i = c * v i := by
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Finset.sum_ite_eq]

/-- Every 15-th root of unity is an eigenvalue of the cyclic shift matrix:
the vector `i ↦ ν ^ i` is an eigenvector for the eigenvalue `ν¹⁴ = ν⁻¹`. -/
lemma root_mem_spectrum_shift {ν : ℂ} (hν : ν ^ 15 = 1) : ν ^ 14 ∈ spectrum ℂ shift := by
  have hmod : ∀ a : ℕ, ν ^ a = ν ^ (a % 15) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a 15]
    rw [pow_add, pow_mul, hν, one_pow, one_mul]
  rw [spectrum.mem_iff]
  intro h
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h
  apply h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => ν ^ (i.val), ?_, ?_⟩
  · intro hzero
    have h0 := congrFun hzero 0
    simp at h0
  · funext i
    have hshift := shift_mulVec (fun i : Fin 15 => ν ^ (i.val)) i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Algebra.algebraMap_eq_smul_one,
      smul_one_mulVec, hshift, Pi.zero_apply]
    rw [← pow_add, hmod (14 + i.val), hmod ((i - 1 : Fin 15)).val]
    have hval : ((i - 1 : Fin 15)).val = (i.val + 14) % 15 := by omega
    rw [hval, Nat.mod_mod_of_dvd _ (dvd_refl 15), sub_eq_zero]
    congr 1

/-- The spectrum of the cyclic shift matrix is exactly the set of 15-th roots of unity. -/
lemma spectrum_shift : spectrum ℂ shift = {ν : ℂ | ν ^ 15 = 1} := by
  ext ν
  constructor
  · intro hv
    have h := spectrum.pow_mem_pow shift 15 hv
    rw [shift_pow_fifteen, spectrum.one_eq] at h
    simpa using h
  · intro (hv : ν ^ 15 = 1)
    have h14 : (ν ^ 14) ^ 15 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]
    have := root_mem_spectrum_shift h14
    rwa [← pow_mul, show 14 * 14 = 15 * 13 + 1 by norm_num, pow_add, pow_mul, hv, one_pow, one_mul,
      pow_one] at this

/-- `exp (2πi/15)` is a 15-th root of unity. -/
lemma exp_pow_fifteen : (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ 15 = 1 := by
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [show (15 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 15) = 2 * (Real.pi : ℂ) * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

/-- For `ν = exp (2πik/15)` one has `ν + ν¹⁴ = ν + ν⁻¹ = 2 cos (2πk/15)`. -/
lemma add_pow_fourteen_eq_two_cos (k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k
        + ((Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k) ^ 14
      = ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ) := by
  set θ : ℂ := ((2 * Real.pi * k / 15 : ℝ) : ℂ) with hθ
  have hw : (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k = Complex.exp (θ * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hne : (Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k ≠ 0 := by
    simp [Complex.exp_ne_zero]
  have h14 : ((Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k) ^ 14
      = ((Complex.exp (2 * Real.pi * Complex.I / 15)) ^ k)⁻¹ := by
    field_simp
    rw [← pow_mul, mul_comm k 15, pow_mul, exp_pow_fifteen, one_pow]
  rw [h14, hw, ← Complex.exp_neg, ← neg_mul, ← Complex.two_cos, hθ]
  push_cast
  ring

/-- **Hückel spectrum of `C₁₅`.**  The eigenvalues of the adjacency matrix of the cycle graph
`C₁₅` are exactly the numbers `2 cos (2πk/15)` for `k = 0, …, 14`. -/
theorem huckel_C15 :
    spectrum ℂ ((SimpleGraph.cycleGraph 15).adjMatrix ℂ) =
      Set.range fun k : Fin 15 => ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ) := by
  have hp : (SimpleGraph.cycleGraph 15).adjMatrix ℂ = aeval shift (X + X ^ 14 : ℂ[X]) := by
    simp [adjMatrix_eq]
  have hdeg : 0 < (X + X ^ 14 : ℂ[X]).degree := by
    have h : (X + X ^ 14 : ℂ[X]).degree = 14 := by compute_degree!
    rw [h]; decide
  rw [hp, spectrum.map_polynomial_aeval_of_degree_pos shift _ hdeg, spectrum_shift]
  have hprim := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  ext μ
  constructor
  · rintro ⟨ν, hν, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hprim.eq_pow_of_pow_eq_one hν
    refine ⟨⟨k, hk⟩, ?_⟩
    simpa using (add_pow_fourteen_eq_two_cos k).symm
  · rintro ⟨k, rfl⟩
    refine ⟨(Complex.exp (2 * Real.pi * Complex.I / 15)) ^ (k : ℕ), ?_, ?_⟩
    · show _ ^ 15 = 1
      rw [← pow_mul, mul_comm (k : ℕ) 15, pow_mul, exp_pow_fifteen, one_pow]
    · simpa using add_pow_fourteen_eq_two_cos (k : ℕ)

end Chem


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

