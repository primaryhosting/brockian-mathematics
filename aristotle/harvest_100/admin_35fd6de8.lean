/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The adjacency matrix of the cycle graph `C₈` (the Hückel matrix of cyclooctatetraene
in units where `α = 0`, `β = 1`), indexed by `Fin 8` with cyclic adjacency. -/
def C8adj : Matrix (Fin 8) (Fin 8) ℂ := fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The candidate eigenvalues, in exponential form. -/
noncomputable def mu (k : Fin 8) : ℂ := zeta ^ (k : ℕ) + zeta ^ (7 * (k : ℕ))

/-- The (unnormalized) discrete Fourier matrix; its columns are the eigenvectors. -/
noncomputable def Fmat : Matrix (Fin 8) (Fin 8) ℂ := fun k j => zeta ^ ((k : ℕ) * (j : ℕ))

/-- The inverse of `Fmat`. -/
noncomputable def Gmat : Matrix (Fin 8) (Fin 8) ℂ :=
  fun k j => zeta ^ (7 * ((k : ℕ) * (j : ℕ))) / 8

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 8 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

lemma zeta_pow_eight : zeta ^ 8 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_mod (a b : ℕ) (h : a % 8 = b % 8) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 8, pow_add, pow_mul, zeta_pow_eight, one_pow, one_mul, h]
  conv_rhs => rw [← Nat.div_add_mod b 8, pow_add, pow_mul, zeta_pow_eight, one_pow, one_mul]

lemma zeta_pow_mul_eight (k : ℕ) : zeta ^ (k * 8) = 1 := by
  simpa using zeta_pow_mod (k * 8) 0 (by omega)

lemma zeta_pow_mul_nine (k : ℕ) : zeta ^ (k * 9) = zeta ^ k := zeta_pow_mod _ _ (by omega)

lemma zeta_pow_mul_ten (k : ℕ) : zeta ^ (k * 10) = zeta ^ (k * 2) := zeta_pow_mod _ _ (by omega)

lemma zeta_pow_mul_eleven (k : ℕ) : zeta ^ (k * 11) = zeta ^ (k * 3) :=
  zeta_pow_mod _ _ (by omega)

lemma zeta_pow_mul_twelve (k : ℕ) : zeta ^ (k * 12) = zeta ^ (k * 4) :=
  zeta_pow_mod _ _ (by omega)

lemma zeta_pow_mul_thirteen (k : ℕ) : zeta ^ (k * 13) = zeta ^ (k * 5) :=
  zeta_pow_mod _ _ (by omega)

lemma zeta_pow_mul_fourteen (k : ℕ) : zeta ^ (k * 14) = zeta ^ (k * 6) :=
  zeta_pow_mod _ _ (by omega)

/-- The columns of the Fourier matrix are eigenvectors of the adjacency matrix. -/
lemma C8adj_mul_Fmat : C8adj * Fmat = Fmat * Matrix.diagonal mu := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [C8adj, Fmat, Fin.sum_univ_eight]
  fin_cases i <;>
    simp +decide [mu, mul_add, ← pow_add, ← Nat.succ_mul, ← Nat.add_mul] <;>
    ring_nf <;>
    simp [zeta_pow_mul_eight, zeta_pow_mul_nine, zeta_pow_mul_ten, zeta_pow_mul_eleven,
      zeta_pow_mul_twelve, zeta_pow_mul_thirteen, zeta_pow_mul_fourteen, add_comm]

/-- Geometric sum of a non-trivial power of `zeta` over a full period vanishes. -/
lemma geom_sum_zeta_eq_zero (m : ℕ) (h : m % 8 ≠ 0) :
    ∑ j : Fin 8, zeta ^ ((j : ℕ) * m) = 0 := by
  set z : ℂ := zeta ^ m with hz
  have hz8 : z ^ 8 = 1 := by
    rw [hz, ← pow_mul, mul_comm, pow_mul, zeta_pow_eight, one_pow]
  have hzne : z ≠ 1 := by
    intro hcon
    have hdvd : (8 : ℕ) ∣ m := (zeta_isPrimitiveRoot.pow_eq_one_iff_dvd m).1 (hz ▸ hcon)
    omega
  have hsum : (z - 1) * (∑ j : Fin 8, z ^ (j : ℕ)) = 0 := by
    rw [Fin.sum_univ_eight]
    have : (z - 1) * (z ^ 0 + z ^ 1 + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7)
        = z ^ 8 - 1 := by ring
    rw [show ((0 : Fin 8) : ℕ) = 0 from rfl]
    simpa [hz8] using this
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.2 hzne
  have hfin : ∑ j : Fin 8, z ^ (j : ℕ) = 0 := by
    rcases mul_eq_zero.1 hsum with h1 | h1
    · exact absurd h1 hzsub
    · exact h1
  calc ∑ j : Fin 8, zeta ^ ((j : ℕ) * m) = ∑ j : Fin 8, z ^ (j : ℕ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hz, ← pow_mul, mul_comm m (j : ℕ)]
    _ = 0 := hfin

lemma geom_sum_zeta_eq_eight (m : ℕ) (h : m % 8 = 0) :
    ∑ j : Fin 8, zeta ^ ((j : ℕ) * m) = 8 := by
  have hterm : ∀ j : Fin 8, zeta ^ ((j : ℕ) * m) = 1 := by
    intro j
    have : ((j : ℕ) * m) % 8 = 0 % 8 := by rw [Nat.mul_mod, h]; simp
    simpa using zeta_pow_mod _ 0 this
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp

lemma mod_eight_iff (k l : Fin 8) : ((k : ℕ) + 7 * (l : ℕ)) % 8 = 0 ↔ k = l := by
  revert k l; decide

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 8,
      Fmat k j * Gmat j l = zeta ^ ((j : ℕ) * ((k : ℕ) + 7 * (l : ℕ))) / 8 := by
    intro j
    simp only [Fmat, Gmat, mul_div_assoc', ← pow_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_div]
  by_cases h : ((k : ℕ) + 7 * (l : ℕ)) % 8 = 0
  · have hkl : k = l := (mod_eight_iff k l).1 h
    subst hkl
    rw [geom_sum_zeta_eq_eight _ h, Matrix.one_apply_eq]
    norm_num
  · rw [geom_sum_zeta_eq_zero _ h, Matrix.one_apply_ne (fun hkl => h ((mod_eight_iff k l).2 hkl))]
    norm_num

lemma Gmat_mul_Fmat : Gmat * Fmat = 1 := mul_eq_one_comm.1 Fmat_mul_Gmat

lemma Gmat_mul_C8adj : Gmat * C8adj = Matrix.diagonal mu * Gmat := by
  calc Gmat * C8adj = Gmat * C8adj * (Fmat * Gmat) := by rw [Fmat_mul_Gmat, mul_one]
    _ = Gmat * (C8adj * Fmat) * Gmat := by simp [mul_assoc]
    _ = Gmat * (Fmat * Matrix.diagonal mu) * Gmat := by rw [C8adj_mul_Fmat]
    _ = Matrix.diagonal mu * Gmat := by
        rw [← mul_assoc Gmat Fmat, Gmat_mul_Fmat, one_mul]

/-- The exponential form of the eigenvalue is the familiar `2 cos (2πk/8)`. -/
lemma mu_eq (k : Fin 8) : mu k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) := by
  have hz : zeta ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz7 : zeta ^ (7 * (k : ℕ))
      = Complex.exp (-((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I)) := by
    have hmul : zeta ^ (7 * (k : ℕ)) * zeta ^ (k : ℕ) = 1 := by
      rw [← pow_add, show 7 * (k : ℕ) + (k : ℕ) = (k : ℕ) * 8 from by ring,
        zeta_pow_mul_eight]
    rw [Complex.exp_neg, ← hz]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [mu, hz, hz7, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- **Hückel theory for cyclooctatetraene / the cycle graph `C₈`.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₈`
if and only if `μ = 2 cos (2πk/8)` for some `k ∈ {0, …, 7}`. -/
theorem huckel_C8 (μ : ℂ) :
    (∃ v : Fin 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      ∃ k : Fin 8, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) := by
  constructor
  · rintro ⟨v, hv, hmul⟩
    set w : Fin 8 → ℂ := Gmat.mulVec v with hw
    have hvw : Fmat.mulVec w = v := by
      rw [hw, Matrix.mulVec_mulVec, Fmat_mul_Gmat, Matrix.one_mulVec]
    have hwne : w ≠ 0 := by
      intro hcon
      apply hv
      rw [← hvw, hcon, Matrix.mulVec_zero]
    have hdiag : (Matrix.diagonal mu).mulVec w = μ • w := by
      rw [hw, Matrix.mulVec_mulVec, ← Gmat_mul_C8adj, ← Matrix.mulVec_mulVec, hmul,
        Matrix.mulVec_smul]
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra hcon
      exact hwne (funext fun k => by simpa using not_not.1 (not_exists.1 hcon k))
    refine ⟨k, ?_⟩
    have := congrFun hdiag k
    rw [Matrix.mulVec_diagonal] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hmu : mu k = μ := mul_right_cancel₀ hk this
    rw [← hmu, mu_eq]
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => Fmat j k, ?_, ?_⟩
    · intro hcon
      have := congrFun hcon 0
      simp [Fmat] at this
    · funext i
      have hcol := congrFun (congrFun C8adj_mul_Fmat i) k
      rw [Matrix.mul_diagonal, Matrix.mul_apply] at hcol
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← mu_eq]
      rw [hcol]
      ring

end Chem

