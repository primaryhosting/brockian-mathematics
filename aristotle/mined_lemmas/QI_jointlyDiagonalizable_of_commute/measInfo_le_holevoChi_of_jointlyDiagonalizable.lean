import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]


theorem measInfo_le_holevoChi_of_jointlyDiagonalizable {p : X → ℝ} {ρ : X → Matrix n n ℂ} {E : Y → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hE : IsPOVM E) (hdiag : JointlyDiagonalizable ρ) :
    measInfo p ρ E ≤ holevoChi p ρ := by
  classical
  obtain ⟨U, hU, hv⟩ := hdiag
  choose v hv using hv
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  set A : Y → n → ℝ := fun y i => ((Uᴴ * E y * U) i i).re with hAdef
  -- the induced classical channel is stochastic
  have hAnn : ∀ y i, 0 ≤ A y i := fun y i =>
    psd_diag_nonneg ((hE.psd y).conjTranspose_mul_mul_same U) i
  have hAcol : ∀ i, ∑ y, A y i = 1 := by
    intro i
    have hsum : ∑ y, Uᴴ * E y * U = (1 : Matrix n n ℂ) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE.sum_eq_one, mul_one, hUU]
    have : ∑ y, A y i = ((∑ y, Uᴴ * E y * U) i i).re := by
      rw [Matrix.sum_apply, hAdef]
      simp
    rw [this, hsum]
    simp
  -- the spectra are nonnegative
  have hD : ∀ x, Uᴴ * ρ x * U = Matrix.diagonal (fun i => (v x i : ℂ)) := by
    intro x
    rw [hv x]
    calc Uᴴ * (U * Matrix.diagonal (fun i => (v x i : ℂ)) * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => (v x i : ℂ)) := by rw [hUU, one_mul, mul_one]
  have hvnn : ∀ x i, 0 ≤ v x i := by
    intro x i
    have h := psd_diag_nonneg ((hens.state x).psd.conjTranspose_mul_mul_same U) i
    rw [hD x] at h
    simpa using h
  -- entropies of the individual states
  have hent : ∀ x, vnEntropy (ρ x) = shannonEntropy (v x) := by
    intro x
    rw [hv x]
    exact vnEntropy_conj_diagonal hU (v x)
  -- the average state
  have havg : avgState p ρ
      = U * Matrix.diagonal (fun i => ((∑ x, p x * v x i : ℝ) : ℂ)) * Uᴴ := by
    rw [avgState]
    have h1 : ∀ x, (p x : ℂ) • ρ x
        = U * ((p x : ℂ) • Matrix.diagonal (fun i => (v x i : ℂ))) * Uᴴ := by
      intro x
      rw [hv x, Matrix.mul_smul, Matrix.smul_mul]
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    congr 1
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_sum, Complex.ofReal_mul]
    · simp [Matrix.sum_apply, h]
  -- outcome probabilities
  have hprob : ∀ x y, outcomeProb (ρ x) (E y) = ∑ i, A y i * v x i := by
    intro x y
    rw [outcomeProb, hv x]
    have h1 : U * Matrix.diagonal (fun i => (v x i : ℂ)) * Uᴴ * E y
        = U * (Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * E y)) := by
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    have h2 : Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * E y) * U
        = Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * E y * U) := by
      simp only [Matrix.mul_assoc]
    rw [h2, trace_diagonal_mul]
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.re_ofReal_mul]
      ring
  -- reduce to the classical statement
  rw [measInfo, holevoChi, havg, vnEntropy_conj_diagonal hU]
  simp only [hprob, hent]
  exact classical_holevo p v A hens.nonneg hvnn hAnn hAcol

/-- **Holevo bound**: the accessible information of a jointly diagonalizable ensemble is at most
its Holevo χ quantity. -/
