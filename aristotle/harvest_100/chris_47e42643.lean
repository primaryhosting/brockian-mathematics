import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₈`; this is the Hückel matrix of
cyclooctatetraene in the units where the Coulomb integral is `0` and the resonance
integral is `1`. -/
noncomputable def C8Adj : Matrix (Fin 8) (Fin 8) ℂ :=
  (SimpleGraph.cycleGraph 8).adjMatrix ℂ

/-- The cyclic shift permutation matrix on `Fin 8`. -/
noncomputable def shift : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (Equiv.addRight (1 : Fin 8))

/-- The inverse cyclic shift permutation matrix on `Fin 8`. -/
noncomputable def shiftInv : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (Equiv.addRight (-1 : Fin 8))

lemma cycleGraph8_adj_iff (i j : Fin 8) :
    (SimpleGraph.cycleGraph 8).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
  rw [SimpleGraph.cycleGraph_adj']
  revert i j
  decide

lemma fin8_sub_one_ne_add_one (i : Fin 8) : (i - 1 : Fin 8) ≠ i + 1 := by revert i; decide

lemma shift_apply (i j : Fin 8) : shift i j = if j = i - 1 then 1 else 0 := by
  simp [shift, Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, sub_eq_add_neg, eq_comm]

lemma shiftInv_apply (i j : Fin 8) : shiftInv i j = if j = i + 1 then 1 else 0 := by
  simp [shiftInv, Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, eq_comm]

lemma shift_mulVec (v : Fin 8 → ℂ) (i : Fin 8) : (shift *ᵥ v) i = v (i - 1) := by
  rw [shift, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  simp [sub_eq_add_neg]

lemma shiftInv_mulVec (v : Fin 8 → ℂ) (i : Fin 8) : (shiftInv *ᵥ v) i = v (i + 1) := by
  rw [shiftInv, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  simp

lemma shift_mul_shiftInv : shift * shiftInv = 1 := by
  rw [shift, shiftInv, ← map_mul]
  have h : (Equiv.addRight (1 : Fin 8)) * (Equiv.addRight (-1 : Fin 8)) = 1 := by
    ext x; simp
  rw [h, map_one]

lemma shift_pow_eight : shift ^ 8 = 1 := by
  rw [shift, ← map_pow]
  have h : ((Equiv.addRight (1 : Fin 8)) ^ 8 : Equiv.Perm (Fin 8)) = 1 := by
    ext x
    simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.coe_addRight, Equiv.Perm.one_apply]
    fin_cases x <;> rfl
  rw [h, map_one]

lemma shift_pow_seven : shift ^ 7 = shiftInv := by
  have h : shift ^ 7 * (shift * shiftInv) = shift ^ 8 * shiftInv := by
    rw [← mul_assoc, ← pow_succ]
  rw [shift_mul_shiftInv, mul_one, shift_pow_eight, one_mul] at h
  exact h

/-- The adjacency matrix of `C₈` is the sum of the cyclic shift and its inverse. -/
lemma C8Adj_eq : C8Adj = shift + shift ^ 7 := by
  rw [shift_pow_seven]
  ext i j
  rw [C8Adj, SimpleGraph.adjMatrix_apply, Matrix.add_apply, shift_apply, shiftInv_apply]
  by_cases h1 : j = i - 1
  · have h2 : ¬ (j = i + 1) := by rw [h1]; exact fin8_sub_one_ne_add_one i
    rw [if_pos ((cycleGraph8_adj_iff i j).2 (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : j = i + 1
    · rw [if_pos ((cycleGraph8_adj_iff i j).2 (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
    · rw [if_neg (fun hA => ((cycleGraph8_adj_iff i j).1 hA).elim h1 h2), if_neg h1, if_neg h2,
        add_zero]

/-- `C₈`'s adjacency matrix is annihilated by `X⁵ - 6X³ + 8X = X(X²-2)(X²-4)`.
This follows purely from `shift ^ 8 = 1`, since modulo `X⁸ - 1` the polynomial
`(X + X⁷)⁵ - 6(X + X⁷)³ + 8(X + X⁷)` vanishes. -/
lemma C8Adj_annihilating : C8Adj ^ 5 - (6 : ℂ) • C8Adj ^ 3 + (8 : ℂ) • C8Adj = 0 := by
  have hnum : ∀ (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ), c • M = (algebraMap ℂ _ c) * M := by
    intro c M
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have key : ((X + X ^ 7) ^ 5 - 6 * (X + X ^ 7) ^ 3 + 8 * (X + X ^ 7) : ℂ[X]) = (X ^ 8 - 1) *
      (-8 * X + 6 * X ^ 3 - X ^ 5 - 8 * X ^ 7 + 10 * X ^ 9 + X ^ 11 - X ^ 13 + 10 * X ^ 15
        + X ^ 19 + 5 * X ^ 21 + X ^ 27) := by
    ring
  have h2 := congrArg (Polynomial.aeval shift) key
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_neg,
    Polynomial.aeval_X] at h2
  rw [shift_pow_eight, sub_self, zero_mul] at h2
  rw [C8Adj_eq, hnum, hnum, map_ofNat, map_ofNat]
  exact h2

/-- Membership in the spectrum of a matrix is exactly the existence of an eigenvector. -/
lemma mem_spectrum_iff_exists_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (mu : ℂ) :
    mu ∈ spectrum ℂ M ↔ ∃ v : Fin n → ℂ, v ≠ 0 ∧ M *ᵥ v = mu • v := by
  have hsm : ∀ v : Fin n → ℂ, (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) mu) *ᵥ v = mu • v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one]
    simp [Matrix.smul_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hmv⟩
    rw [sub_mulVec, sub_eq_zero] at hmv
    exact ⟨v, hv, by rw [← hmv, hsm]⟩
  · rintro ⟨v, hv, hmv⟩
    exact ⟨v, hv, by rw [sub_mulVec, sub_eq_zero, hmv, hsm]⟩

lemma pow_mulVec_eigen {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {mu : ℂ}
    (h : M *ᵥ v = mu • v) (m : ℕ) : (M ^ m) *ᵥ v = mu ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]

/-- For each `k`, the vector `i ↦ exp(2πik/8)ⁱ` is an eigenvector of `C8Adj`
with eigenvalue `2 cos (2πk/8)`. -/
lemma C8Adj_hasEigenvector (k : Fin 8) :
    ∃ v : Fin 8 → ℂ, v ≠ 0 ∧
      C8Adj *ᵥ v = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ) • v := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 8 with ht
  set z : ℂ := Complex.exp ((t : ℂ) * Complex.I) with hz
  have hz8 : z ^ 8 = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have h : (8 : ℕ) * ((t : ℂ) * Complex.I) = ((k : ℕ) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [ht]; push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hzne : z ≠ 0 := Complex.exp_ne_zero _
  have hzinv : z ^ 7 = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have h1 : z * z ^ 7 = 1 := by rw [← pow_succ']; exact hz8
    have h2 : z * Complex.exp (-((t : ℂ) * Complex.I)) = 1 := by
      rw [hz, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    exact mul_left_cancel₀ hzne (h1.trans h2.symm)
  have hsum : z + z ^ 7 = ((2 * Real.cos t : ℝ) : ℂ) := by
    rw [hzinv, hz, Complex.exp_mul_I,
      show -((t : ℂ) * Complex.I) = (-(t : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    push_cast [Complex.ofReal_cos]
    ring
  have hmod : ∀ a : ℕ, z ^ a = z ^ (a % 8) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a 8]
    rw [pow_add, pow_mul, hz8, one_pow, one_mul]
  have hs1 : ∀ i : Fin 8, ((i - 1 : Fin 8) : ℕ) = (7 + (i : ℕ)) % 8 := by decide
  have hs2 : ∀ i : Fin 8, ((i + 1 : Fin 8) : ℕ) = (1 + (i : ℕ)) % 8 := by decide
  refine ⟨fun i => z ^ ((i : ℕ)), ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · funext i
    rw [C8Adj_eq, shift_pow_seven, Matrix.add_mulVec, Pi.add_apply, shift_mulVec, shiftInv_mulVec,
      Pi.smul_apply, smul_eq_mul, ← hsum, hs1 i, hs2 i, ← hmod, ← hmod, pow_add, pow_add]
    ring

/-- **Hückel theory for cyclooctatetraene (C₈).**
The spectrum of the adjacency matrix of the cycle graph `C₈` is exactly
`{2 cos (2πk/8) : k = 0, …, 7}`. -/
theorem huckel_C8 :
    spectrum ℂ C8Adj =
      Set.range (fun k : Fin 8 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ)) := by
  have c0 : Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 8) = 1 := by norm_num
  have c1 : Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 8) = Real.sqrt 2 / 2 := by
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 8) = Real.pi / 4 by push_cast; ring,
      Real.cos_pi_div_four]
  have c2 : Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 8) = 0 := by
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 8) = Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
  have c3 : Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 8) = -(Real.sqrt 2 / 2) := by
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 8) = Real.pi - Real.pi / 4 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
  have c4 : Real.cos (2 * Real.pi * ((4 : ℕ) : ℝ) / 8) = -1 := by
    rw [show (2 * Real.pi * ((4 : ℕ) : ℝ) / 8) = Real.pi by push_cast; ring, Real.cos_pi]
  apply Set.eq_of_subset_of_subset
  · intro mu hmu
    obtain ⟨v, hv, hmv⟩ := (mem_spectrum_iff_exists_eigenvector C8Adj mu).1 hmu
    have hpoly : mu ^ 5 - (6 : ℂ) * mu ^ 3 + (8 : ℂ) * mu = 0 := by
      have hsmul : (mu ^ 5 - (6 : ℂ) * mu ^ 3 + (8 : ℂ) * mu) • v = 0 := by
        have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => M *ᵥ v) C8Adj_annihilating
        simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec,
          pow_mulVec_eigen hmv, hmv] at h
        rw [add_smul, sub_smul, SemigroupAction.mul_smul, SemigroupAction.mul_smul]
        exact h
      rcases smul_eq_zero.1 hsmul with h | h
      · exact h
      · exact absurd h hv
    have hr2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      norm_cast
      rw [Real.sq_sqrt]; norm_num
    have hfac : mu * ((mu - 2) * (mu + 2)) *
        ((mu - (Real.sqrt 2 : ℝ)) * (mu + (Real.sqrt 2 : ℝ))) = 0 := by
      linear_combination hpoly + (4 * mu - mu ^ 3) * hr2
    rcases mul_eq_zero.1 hfac with h | h
    · rcases mul_eq_zero.1 h with h | h
      · refine ⟨2, ?_⟩
        show ((2 * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 8) : ℝ) : ℂ) = mu
        rw [c2, h]; norm_num
      · rcases mul_eq_zero.1 h with h | h
        · refine ⟨0, ?_⟩
          show ((2 * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 8) : ℝ) : ℂ) = mu
          rw [c0]; push_cast; linear_combination -h
        · refine ⟨4, ?_⟩
          show ((2 * Real.cos (2 * Real.pi * ((4 : ℕ) : ℝ) / 8) : ℝ) : ℂ) = mu
          rw [c4]; push_cast; linear_combination -h
    · rcases mul_eq_zero.1 h with h | h
      · refine ⟨1, ?_⟩
        show ((2 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 8) : ℝ) : ℂ) = mu
        rw [c1]; push_cast; linear_combination -h
      · refine ⟨3, ?_⟩
        show ((2 * Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 8) : ℝ) : ℂ) = mu
        rw [c3]; push_cast; linear_combination -h
  · rintro _ ⟨k, rfl⟩
    exact (mem_spectrum_iff_exists_eigenvector C8Adj _).2 (C8Adj_hasEigenvector k)

end Chem

