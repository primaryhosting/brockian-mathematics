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

/-!
# Hückel theory for the cycle C₂₀

The adjacency eigenvalues of the cycle graph `C₂₀` are `2 * cos (2 π k / 20)`, `k = 0, …, 19`.

We prove this by explicitly diagonalizing the adjacency matrix with the discrete Fourier
transform matrix `U i k = ζ (i * k)`, where `ζ m = exp (2 π i m / 20)`.
-/

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- `ζ m = exp (2 π i m / 20)`, a 20-th root of unity raised to the power `m`. -/
noncomputable def zeta (m : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * m / 20)

lemma zeta_add (a b : ℤ) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, ← Complex.exp_add]
  push_cast
  ring_nf

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_twenty_mul (t : ℤ) : zeta (20 * t) = 1 := by
  have := Complex.exp_int_mul_two_pi_mul_I t
  rw [zeta]
  rw [show ((2 : ℂ) * Real.pi * Complex.I * ((20 * t : ℤ) : ℂ) / 20)
      = (t : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact this

lemma zeta_congr {a b : ℤ} (h : (20 : ℤ) ∣ b - a) : zeta a = zeta b := by
  obtain ⟨t, ht⟩ := h
  have : b = a + 20 * t := by omega
  rw [this, zeta_add, zeta_twenty_mul, mul_one]

lemma zeta_eq_one_iff {m : ℤ} : zeta m = 1 ↔ (20 : ℤ) ∣ m := by
  constructor
  · intro h
    rw [zeta, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp at hn
    have hm : m = 20 * n := by exact_mod_cast hn
    exact ⟨n, hm⟩
  · rintro ⟨t, rfl⟩
    exact zeta_twenty_mul t

lemma zeta_natCast_mul (n : ℕ) (m : ℤ) : zeta (n * m) = zeta m ^ n := by
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The adjacency matrix of the cycle graph `C₂₀`, over `ℂ`. -/
noncomputable def A : Matrix (Fin 20) (Fin 20) ℂ := (SimpleGraph.cycleGraph 20).adjMatrix ℂ

/-- The Hückel eigenvalues `2 cos (2 π k / 20)`. -/
noncomputable def lam (k : Fin 20) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 20)

/-- The discrete Fourier transform matrix. -/
noncomputable def U : Matrix (Fin 20) (Fin 20) ℂ := fun i k => zeta ((i : ℕ) * (k : ℕ))

/-- The (scaled) inverse Fourier matrix. -/
noncomputable def V : Matrix (Fin 20) (Fin 20) ℂ := fun i k => zeta (-((i : ℕ) * (k : ℕ)))

lemma lam_eq (k : Fin 20) : lam k = zeta (k : ℕ) + zeta (-(k : ℕ)) := by
  have h1 : zeta ((k : ℕ) : ℤ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 20 : ℝ) * Complex.I) := by
    rw [zeta]; congr 1; push_cast; ring
  have h2 : zeta (-((k : ℕ) : ℤ)) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta]; congr 1; push_cast; ring
  rw [lam, h1, h2, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- Fin-valued addition is compatible with `zeta`'s argument modulo 20. -/
lemma val_add_congr (i j : Fin 20) : (20 : ℤ) ∣ ((i + j : Fin 20) : ℕ) - ((i : ℕ) + (j : ℕ)) := by
  have : ((i + j : Fin 20) : ℕ) = ((i : ℕ) + (j : ℕ)) % 20 := by
    simp [Fin.val_add]
  rw [this]
  have := Nat.div_add_mod ((i : ℕ) + (j : ℕ)) 20
  refine ⟨-(((i : ℕ) + (j : ℕ)) / 20 : ℕ), ?_⟩
  omega

lemma U_shift (i j : Fin 20) (k : Fin 20) :
    U (i + j) k = U i k * zeta ((j : ℕ) * (k : ℕ)) := by
  rw [U, U, ← zeta_add]
  refine zeta_congr ?_
  obtain ⟨t, ht⟩ := val_add_congr i j
  refine ⟨-(t * ((k : ℕ) : ℤ)), ?_⟩
  linear_combination (-(((k : ℕ) : ℤ))) * ht

lemma neighbor_sum (i k : Fin 20) :
    (A * U) i k = U (i - 1) k + U (i + 1) k := by
  have hne : i - 1 ≠ i + 1 := by
    intro hc
    have h1 : (i - 1) + 1 = (i + 1) + 1 := by rw [hc]
    rw [sub_add_cancel] at h1
    have hone : (1 : Fin 20) + 1 = 2 := by decide
    have h2 : i + 2 = i + 0 := by
      rw [add_zero]
      conv_rhs => rw [h1]
      rw [add_assoc, hone]
    have h3 : (2 : Fin 20) = 0 := add_left_cancel h2
    exact absurd h3 (by decide)
  have h2 : (A * U) i k
      = ((SimpleGraph.cycleGraph 20).adjMatrix ℂ *ᵥ (fun j => U j k)) i := by
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h2, SimpleGraph.adjMatrix_mulVec_apply]
  rw [show (20 : ℕ) = 18 + 2 from rfl] at *
  rw [SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]

lemma A_mul_U : A * U = U * Matrix.diagonal lam := by
  ext i k
  rw [neighbor_sum]
  have h1 : U (i + 1) k = U i k * zeta ((k : ℕ) : ℤ) := by
    have := U_shift i 1 k
    simpa using this
  have h2 : U (i - 1) k = U i k * zeta (-((k : ℕ) : ℤ)) := by
    have h := U_shift (i - 1) 1 k
    rw [sub_add_cancel] at h
    have hz : zeta (((1 : Fin 20) : ℕ) * (k : ℕ)) * zeta (-((k : ℕ) : ℤ)) = 1 := by
      rw [← zeta_add]
      simpa using zeta_zero
    calc U (i - 1) k = U (i - 1) k * (zeta (((1 : Fin 20) : ℕ) * (k : ℕ)) * zeta (-((k : ℕ) : ℤ))) := by
          rw [hz, mul_one]
      _ = (U (i - 1) k * zeta (((1 : Fin 20) : ℕ) * (k : ℕ))) * zeta (-((k : ℕ) : ℤ)) := by ring
      _ = U i k * zeta (-((k : ℕ) : ℤ)) := by rw [← h]
  rw [h1, h2, Matrix.mul_diagonal, lam_eq]
  ring

lemma geom_sum_zeta (m : ℤ) :
    ∑ j : Fin 20, zeta ((j : ℕ) * m) = if (20 : ℤ) ∣ m then 20 else 0 := by
  have hpow : ∀ j : Fin 20, zeta ((j : ℕ) * m) = zeta m ^ (j : ℕ) := fun j =>
    zeta_natCast_mul (j : ℕ) m
  simp only [hpow]
  rw [Fin.sum_univ_eq_sum_range (fun n => zeta m ^ n) 20]
  by_cases h : (20 : ℤ) ∣ m
  · have : zeta m = 1 := zeta_eq_one_iff.mpr h
    simp [this, h]
  · have hne : zeta m ≠ 1 := fun hc => h (zeta_eq_one_iff.mp hc)
    have h20 : zeta m ^ (20 : ℕ) = 1 := by
      rw [← zeta_natCast_mul 20 m]
      exact zeta_twenty_mul m
    rw [geom_sum_eq hne, h20]
    simp [h]

lemma U_mul_V : U * V = (20 : ℂ) • (1 : Matrix (Fin 20) (Fin 20) ℂ) := by
  ext i k
  have : (U * V) i k = ∑ j : Fin 20, zeta ((j : ℕ) * (((i : ℕ) : ℤ) - (k : ℕ))) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [U, V, ← zeta_add]
    congr 1
    ring
  rw [this, geom_sum_zeta]
  by_cases hik : i = k
  · subst hik
    simp
  · have : ¬ ((20 : ℤ) ∣ (((i : ℕ) : ℤ) - (k : ℕ))) := by
      have hi := i.isLt
      have hk := k.isLt
      have : (i : ℕ) ≠ (k : ℕ) := fun hc => hik (Fin.ext hc)
      omega
    simp [this, Matrix.one_apply_ne hik]

lemma isUnit_det_U : IsUnit U.det := by
  refine Matrix.isUnit_det_of_right_inverse (B := (20 : ℂ)⁻¹ • V) ?_
  rw [Matrix.mul_smul, U_mul_V, smul_smul]
  norm_num

theorem charpoly_A : A.charpoly = ∏ k : Fin 20, (X - C (lam k)) := by
  set M : (Matrix (Fin 20) (Fin 20) ℂ)ˣ := Matrix.nonsingInvUnit U isUnit_det_U with hM
  have hMval : (M : Matrix (Fin 20) (Fin 20) ℂ) = U := rfl
  have hMinv : ((M⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) = U⁻¹ := rfl
  have hA : A = (M : Matrix (Fin 20) (Fin 20) ℂ) * Matrix.diagonal lam
      * ((M⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
    rw [hMval, hMinv, ← A_mul_U, Matrix.mul_assoc, Matrix.mul_nonsing_inv U isUnit_det_U,
      Matrix.mul_one]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel theory for C₂₀.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₂₀` factors as `∏_{k=0}^{19} (X - 2 cos (2 π k / 20))`; equivalently, the adjacency
eigenvalues of `C₂₀` are `2 cos (2 π k / 20)` for `k = 0, …, 19` (listed with multiplicity). -/
theorem huckel_C20 :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).charpoly =
      ∏ k : Fin 20, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)) := by
  have := charpoly_A
  simpa [A, lam] using this

/-- The spectrum of the adjacency matrix of `C₂₀` is exactly the set of numbers
`2 cos (2 π k / 20)`, `k = 0, …, 19`. -/
theorem huckel_C20_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : Fin 20, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C20]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Set.mem_setOf_eq]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, sub_eq_zero]

/-- The real form of the Hückel result: the characteristic polynomial of the real adjacency
matrix of `C₂₀` factors as `∏_{k=0}^{19} (X - 2 cos (2 π k / 20))`. -/
theorem huckel_C20_real :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℝ).charpoly =
      ∏ k : Fin 20, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 20))) := by
  have hmap : ((SimpleGraph.cycleGraph 20).adjMatrix ℝ).map (algebraMap ℝ ℂ)
      = (SimpleGraph.cycleGraph 20).adjMatrix ℂ := by
    ext i j
    by_cases h : (SimpleGraph.cycleGraph 20).Adj i j <;>
      simp [SimpleGraph.adjMatrix_apply, h]
  have h := huckel_C20
  rw [← hmap, Matrix.charpoly_map] at h
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  rw [h, Polynomial.map_prod]
  simp

/-- Explicit Hückel molecular orbitals: for each `k`, the vector `j ↦ exp (2 π i j k / 20)` is a
nonzero eigenvector of the adjacency matrix of `C₂₀` with eigenvalue `2 cos (2 π k / 20)`. -/
theorem huckel_C20_eigenvector (k : Fin 20) :
    (fun j : Fin 20 => zeta ((j : ℕ) * (k : ℕ))) ≠ 0 ∧
      (SimpleGraph.cycleGraph 20).adjMatrix ℂ *ᵥ (fun j : Fin 20 => zeta ((j : ℕ) * (k : ℕ)))
        = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) •
            (fun j : Fin 20 => zeta ((j : ℕ) * (k : ℕ))) := by
  constructor
  · intro hc
    have h0 : zeta ((((0 : Fin 20) : ℕ) : ℤ) * ((k : ℕ) : ℤ)) = 0 := congrFun hc 0
    rw [show ((((0 : Fin 20) : ℕ) : ℤ) * ((k : ℕ) : ℤ)) = 0 by simp, zeta_zero] at h0
    exact one_ne_zero h0
  · funext i
    have h1 : ((SimpleGraph.cycleGraph 20).adjMatrix ℂ *ᵥ
        (fun j : Fin 20 => zeta ((j : ℕ) * (k : ℕ)))) i = (A * U) i k := by
      simp [A, U, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, A_mul_U, Matrix.mul_diagonal]
    simp [U, lam, Pi.smul_apply, mul_comm]

end Chem

