import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/
noncomputable def C19 : Matrix (Fin 19) (Fin 19) ℂ := (SimpleGraph.cycleGraph 19).adjMatrix ℂ

/-- A primitive 19-th root of unity. -/
noncomputable def zeta19 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

lemma zeta19_isPrimitiveRoot : IsPrimitiveRoot zeta19 19 := by
  simpa [zeta19] using Complex.isPrimitiveRoot_exp 19 (by norm_num)

lemma zeta19_pow_nineteen : zeta19 ^ 19 = 1 := zeta19_isPrimitiveRoot.pow_eq_one

/-- `w ^ m` only depends on `m % 19` when `w ^ 19 = 1`. -/
lemma pow_mod_nineteen {w : ℂ} (hw : w ^ 19 = 1) (m : ℕ) : w ^ m = w ^ (m % 19) := by
  conv_lhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, hw, one_pow, one_mul]

lemma pow_val_add_one {w : ℂ} (hw : w ^ 19 = 1) (i : Fin 19) :
    w ^ ((i + 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w := by
  have h : ((i + 1 : Fin 19) : ℕ) = ((i : ℕ) + 1) % 19 := by
    simp [Fin.val_add]
  rw [h, ← pow_mod_nineteen hw, pow_succ]

lemma pow_val_sub_one {w : ℂ} (hw : w ^ 19 = 1) (i : Fin 19) :
    w ^ ((i - 1 : Fin 19) : ℕ) * w = w ^ (i : ℕ) := by
  have h := pow_val_add_one hw (i - 1)
  rw [sub_add_cancel] at h
  exact h.symm

/-- The basic eigenvector computation: for any 19-th root of unity `w`, the geometric
vector `j ↦ w ^ j` is an eigenvector of the adjacency matrix of `C₁₉` with
eigenvalue `w + w⁻¹`. -/
lemma C19_mulVec_geom {w : ℂ} (hw : w ^ 19 = 1) :
    C19 *ᵥ (fun j : Fin 19 => w ^ (j : ℕ)) = (w + w⁻¹) • (fun j : Fin 19 => w ^ (j : ℕ)) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; norm_num at hw
  funext i
  have hne : (i - 1 : Fin 19) ≠ i + 1 := by revert i; decide
  have hnb : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i)
  rw [C19, SimpleGraph.adjMatrix_mulVec_apply, hnb, Finset.sum_pair hne]
  have h1 : w ^ ((i - 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w⁻¹ := by
    field_simp
    exact pow_val_sub_one hw i
  rw [h1, pow_val_add_one hw i]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `exp (θ i) + exp (θ i)⁻¹ = 2 cos θ`. -/
lemma exp_add_inv_exp (θ : ℝ) :
    Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹
      = ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The `k`-th Hückel eigenvector of `C₁₉`. -/
noncomputable def evec (k : ℕ) : Fin 19 → ℂ := fun j => (zeta19 ^ k) ^ (j : ℕ)

lemma evec_ne_zero (k : ℕ) : evec k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [evec] at h0

lemma zeta19_pow_eq (k : ℕ) : zeta19 ^ k = Complex.exp (((2 * Real.pi * k / 19 : ℝ) : ℂ) * I) := by
  rw [zeta19, ← Complex.exp_nsmul]
  congr 1
  push_cast
  ring

lemma C19_mulVec_evec (k : ℕ) :
    C19 *ᵥ evec k = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) • evec k := by
  have hw : (zeta19 ^ k) ^ 19 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta19_pow_nineteen, one_pow]
  have h := C19_mulVec_geom hw
  rw [show (fun j : Fin 19 => (zeta19 ^ k) ^ (j : ℕ)) = evec k from rfl] at h
  rw [h, zeta19_pow_eq k, exp_add_inv_exp]

/-- The Vandermonde matrix whose `k`-th column is the `k`-th eigenvector. -/
noncomputable def V19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.vandermonde (fun j : Fin 19 => zeta19 ^ (j : ℕ))

lemma V19_apply (j k : Fin 19) : V19 j k = evec (k : ℕ) j := by
  simp only [V19, Matrix.vandermonde_apply, evec, ← pow_mul, mul_comm]

lemma V19_det_ne_zero : V19.det ≠ 0 := by
  rw [V19]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b hab
  exact Fin.ext (zeta19_isPrimitiveRoot.pow_inj a.isLt b.isLt hab)

lemma V19_isUnit_det : IsUnit V19.det := isUnit_iff_ne_zero.mpr V19_det_ne_zero

/-- Diagonal matrix of the Hückel eigenvalues of `C₁₉`. -/
noncomputable def D19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.diagonal (fun k : Fin 19 => ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ))

lemma C19_mul_V19 : C19 * V19 = V19 * D19 := by
  ext i k
  have h : ∑ j, C19 i j * evec (k : ℕ) j
      = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) * evec (k : ℕ) i := by
    have h0 := congrFun (C19_mulVec_evec (k : ℕ)) i
    simpa [Matrix.mulVec, dotProduct] using h0
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc ∑ j, C19 i j * V19 j k = ∑ j, C19 i j * evec (k : ℕ) j := by
        simp only [V19_apply]
    _ = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) * evec (k : ℕ) i := h
    _ = ∑ j, V19 i j * D19 j k := by
        rw [← Matrix.mul_apply, D19, Matrix.mul_diagonal, V19_apply]
        ring

lemma V19_mulVec_injective {x y : Fin 19 → ℂ} (h : V19 *ᵥ x = V19 *ᵥ y) : x = y := by
  have := congrArg (fun z => V19⁻¹ *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul V19 V19_isUnit_det] using this

/-- **Hückel theory for C₁₉.** A complex number `μ` is an eigenvalue of the adjacency
(Hückel) matrix of the cycle graph `C₁₉` if and only if `μ = 2 cos (2πk/19)` for some
`k ∈ {0, 1, …, 18}`. -/
theorem huckel_C19 (μ : ℂ) :
    (∃ v : Fin 19 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 19).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 19 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    rw [← show C19 = (SimpleGraph.cycleGraph 19).adjMatrix ℂ from rfl] at hv
    set w : Fin 19 → ℂ := V19⁻¹ *ᵥ v with hw
    have hVw : V19 *ᵥ w = v := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V19 V19_isUnit_det,
        Matrix.one_mulVec]
    have hDw : D19 *ᵥ w = μ • w := by
      refine V19_mulVec_injective ?_
      rw [Matrix.mulVec_mulVec, ← C19_mul_V19, ← Matrix.mulVec_mulVec, hVw, hv,
        Matrix.mulVec_smul, hVw]
    have hw0 : w ≠ 0 := by
      intro h
      apply hv0
      rw [← hVw, h, Matrix.mulVec_zero]
    obtain ⟨k, hk⟩ : ∃ k : Fin 19, w k ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hw0 (funext fun k => hc k)
    refine ⟨(k : ℕ), k.isLt, ?_⟩
    have := congrFun hDw k
    rw [D19, Matrix.mulVec_diagonal] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hk this).symm
  · rintro ⟨k, hk, rfl⟩
    exact ⟨evec k, evec_ne_zero k, C19_mulVec_evec k⟩

/-- Membership in the spectrum of a square complex matrix is the existence of a nonzero
eigenvector. -/
lemma mem_spectrum_iff_exists_eigenvector (A : Matrix (Fin 19) (Fin 19) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ v : Fin 19 → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  have key : ∀ v : Fin 19 → ℂ,
      (algebraMap ℂ (Matrix (Fin 19) (Fin 19) ℂ) μ - A) *ᵥ v = μ • v - A *ᵥ v := by
    intro v
    simp [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (sub_eq_zero.mp (key v ▸ h)).symm⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, h, sub_self]⟩

/-- **Hückel spectrum of C₁₉.** The spectrum of the adjacency (Hückel) matrix of the
cycle graph `C₁₉` is exactly `{2 cos (2πk/19) : k = 0, …, 18}`. -/
theorem huckel_C19_spectrum :
    spectrum ℂ C19 =
      {μ : ℂ | ∃ k : ℕ, k < 19 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)} := by
  ext μ
  rw [mem_spectrum_iff_exists_eigenvector]
  exact huckel_C19 μ

end Chem

