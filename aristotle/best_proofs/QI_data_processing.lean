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

import RequestProject.QI.KadisonSchwarz

/-!
# A variational formula for the resolvent quantity `G`

For positive semidefinite `ρ`, `σ` and `t ≥ 0` we consider the concave functional

`energy ρ σ t X = 2 Re Tr (ρ X) - Re Tr (Xᴴ σ X) - t Re Tr (Xᴴ X ρ)`

and its supremum `Gfun ρ σ t`.  This is a variational form of
`⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫` for the relative modular operator `Δ : Z ↦ σ Z ρ⁻¹`.

Two facts are proved here:

* `Gfun` is computed by any stationary point (`Gfun_eq_of_stationary`), and a stationary
  point exists whenever `σ` is positive definite, with an explicit spectral value
  (`Gfun_spectral`);
* `Gfun` is monotone under quantum channels (`Gfun_krausMap_le`).
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- The concave functional whose supremum is `Gfun`. -/
noncomputable def energy (ρ σ : Matrix n n ℂ) (t : ℝ) (X : Matrix n n ℂ) : ℝ :=
  2 * (Matrix.trace (ρ * X)).re - (Matrix.trace (Xᴴ * σ * X)).re -
    t * (Matrix.trace (Xᴴ * X * ρ)).re

/-- The supremum of `energy`. -/
noncomputable def Gfun (ρ σ : Matrix n n ℂ) (t : ℝ) : ℝ := sSup (Set.range (energy ρ σ t))

/-! ### Completing the square -/

section Stationary

variable {ρ σ : Matrix n n ℂ} {t : ℝ} {X₀ : Matrix n n ℂ}

omit [DecidableEq n] in
theorem trace_conjTranspose_mul_mul (hρ : ρ.IsHermitian) (Z : Matrix n n ℂ) :
    Matrix.trace (X₀ᴴ * Z * ρ) = Matrix.trace ((X₀ * ρ)ᴴ * Z) := by
  have h : (X₀ * ρ)ᴴ * Z = ρ * (X₀ᴴ * Z) := by
    rw [Matrix.conjTranspose_mul, hρ.eq, Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm ρ (X₀ᴴ * Z), Matrix.mul_assoc]

/-- The stationarity identity: the derivative of `energy` at `X₀` vanishes. -/
theorem trace_stationary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) (Z : Matrix n n ℂ) :
    Matrix.trace (X₀ᴴ * σ * Z) + (t : ℂ) * Matrix.trace (X₀ᴴ * Z * ρ)
      = Matrix.trace (ρ * Z) := by
  have e1 : Matrix.trace (X₀ᴴ * σ * Z) = Matrix.trace ((σ * X₀)ᴴ * Z) := by
    rw [Matrix.conjTranspose_mul, hσ.eq]
  have key : (σ * X₀ + (t : ℂ) • (X₀ * ρ))ᴴ * Z
      = (σ * X₀)ᴴ * Z + (t : ℂ) • ((X₀ * ρ)ᴴ * Z) := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul]
  rw [hX₀] at key
  have h := congrArg Matrix.trace key
  rw [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, hρ.eq] at h
  rw [e1, trace_conjTranspose_mul_mul hρ Z, ← h]

theorem trace_stationary_re (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) (Z : Matrix n n ℂ) :
    (Matrix.trace (X₀ᴴ * σ * Z)).re + t * (Matrix.trace (X₀ᴴ * Z * ρ)).re
      = (Matrix.trace (ρ * Z)).re := by
  have h := congrArg Complex.re (trace_stationary hρ hσ hX₀ Z)
  simpa [Complex.add_re, Complex.mul_re] using h

theorem energy_add (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) (Z : Matrix n n ℂ) :
    energy ρ σ t (X₀ + Z) =
      energy ρ σ t X₀ -
        ((Matrix.trace (Zᴴ * σ * Z)).re + t * (Matrix.trace (Zᴴ * Z * ρ)).re) := by
  have hcross1 : (Matrix.trace (Zᴴ * σ * X₀)).re = (Matrix.trace (X₀ᴴ * σ * Z)).re := by
    have h : (X₀ᴴ * σ * Z)ᴴ = Zᴴ * σ * X₀ := by
      simp [Matrix.conjTranspose_mul, hσ.eq, Matrix.mul_assoc]
    rw [← h, Matrix.trace_conjTranspose]
    simp
  have hcross2 : (Matrix.trace (Zᴴ * X₀ * ρ)).re = (Matrix.trace (X₀ᴴ * Z * ρ)).re := by
    have h : (X₀ᴴ * Z * ρ)ᴴ = ρ * Zᴴ * X₀ := by
      simp [Matrix.conjTranspose_mul, hρ.eq, Matrix.mul_assoc]
    have h2 : Matrix.trace (ρ * Zᴴ * X₀) = Matrix.trace (Zᴴ * X₀ * ρ) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [← h2, ← h, Matrix.trace_conjTranspose]
    simp
  have hA : Matrix.trace (ρ * (X₀ + Z)) = Matrix.trace (ρ * X₀) + Matrix.trace (ρ * Z) := by
    rw [Matrix.mul_add, Matrix.trace_add]
  have hB : Matrix.trace ((X₀ + Z)ᴴ * σ * (X₀ + Z)) =
      Matrix.trace (X₀ᴴ * σ * X₀) + Matrix.trace (X₀ᴴ * σ * Z) + Matrix.trace (Zᴴ * σ * X₀)
        + Matrix.trace (Zᴴ * σ * Z) := by
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    ring
  have hC : Matrix.trace ((X₀ + Z)ᴴ * (X₀ + Z) * ρ) =
      Matrix.trace (X₀ᴴ * X₀ * ρ) + Matrix.trace (X₀ᴴ * Z * ρ) + Matrix.trace (Zᴴ * X₀ * ρ)
        + Matrix.trace (Zᴴ * Z * ρ) := by
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    ring
  have hst := trace_stationary_re hρ hσ hX₀ Z
  simp only [energy, hA, hB, hC, Complex.add_re]
  linear_combination (-2 : ℝ) * hst - hcross1 - t * hcross2

theorem energy_stationary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) :
    energy ρ σ t X₀ = (Matrix.trace (ρ * X₀)).re := by
  have hst := trace_stationary_re hρ hσ hX₀ X₀
  simp only [energy]
  linarith

theorem energy_le_stationary (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) (X : Matrix n n ℂ) :
    energy ρ σ t X ≤ energy ρ σ t X₀ := by
  have := energy_add hρ.isHermitian hσ.isHermitian hX₀ (X - X₀)
  rw [add_sub_cancel] at this
  have h1 : 0 ≤ (Matrix.trace ((X - X₀)ᴴ * σ * (X - X₀))).re := by
    have : ((X - X₀)ᴴ * σ * (X - X₀)).PosSemidef := hσ.conjTranspose_mul_mul_same _
    exact (Complex.le_def.mp this.trace_nonneg).1
  have h2 : 0 ≤ (Matrix.trace ((X - X₀)ᴴ * (X - X₀) * ρ)).re := by
    have hpsd : ((X - X₀)ᴴ * (X - X₀)).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
    exact trace_mul_re_nonneg hpsd hρ
  nlinarith [mul_nonneg ht h2]

theorem isGreatest_energy (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) :
    IsGreatest (Set.range (energy ρ σ t)) (energy ρ σ t X₀) :=
  ⟨⟨X₀, rfl⟩, by rintro _ ⟨X, rfl⟩; exact energy_le_stationary hρ hσ ht hX₀ X⟩

theorem Gfun_eq_of_stationary (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) :
    Gfun ρ σ t = (Matrix.trace (ρ * X₀)).re := by
  rw [Gfun, (isGreatest_energy hρ hσ ht hX₀).csSup_eq,
    energy_stationary hρ.isHermitian hσ.isHermitian hX₀]

end Stationary

/-! ### Existence of a stationary point and the spectral formula -/

section Spectral

variable {ρ σ : Matrix n n ℂ} {t : ℝ}

/-- Entrywise solution of the Sylvester equation in the joint eigenbasis. -/
noncomputable def sylvesterCoeff (r s : n → ℝ) (t : ℝ) (C : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun j k => ((r k / (s j + t * r k) : ℝ) : ℂ) * C j k

theorem sylvester_solve (r s : n → ℝ) (t : ℝ) (C : Matrix n n ℂ)
    (h : ∀ j k, s j + t * r k ≠ 0) :
    diagonal (fun j => (s j : ℂ)) * sylvesterCoeff r s t C
      + (t : ℂ) • (sylvesterCoeff r s t C * diagonal (fun k => (r k : ℂ)))
      = C * diagonal (fun k => (r k : ℂ)) := by
  ext j k
  simp only [sylvesterCoeff, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.of_apply, smul_eq_mul]
  have hd : s j + t * r k ≠ 0 := h j k
  have hd' : r k * t + s j ≠ 0 := by rw [mul_comm, ← add_comm]; exact hd
  have hs : ((r k / (s j + t * r k)) * s j + t * ((r k / (s j + t * r k)) * r k)) = r k := by
    have e : (r k / (s j + t * r k)) * s j + t * ((r k / (s j + t * r k)) * r k)
        = (r k * (s j + t * r k)) / (s j + t * r k) := by
      field_simp
    rw [e, mul_div_assoc, div_self hd, mul_one]
  have hsC := congrArg (fun x : ℝ => (x : ℂ)) hs
  push_cast at hsC ⊢
  linear_combination C j k * hsC

theorem stationary_of_spectral {ρ σ : Matrix n n ℂ} {t : ℝ} (U W : Matrix n n ℂ) (r s : n → ℝ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (hW : Wᴴ * W = 1)
    (hσe : σ = U * diagonal (fun j => (s j : ℂ)) * Uᴴ)
    (hρe : ρ = W * diagonal (fun k => (r k : ℂ)) * Wᴴ)
    (hne : ∀ j k, s j + t * r k ≠ 0) :
    σ * (U * sylvesterCoeff r s t (Uᴴ * W) * Wᴴ)
      + (t : ℂ) • (U * sylvesterCoeff r s t (Uᴴ * W) * Wᴴ * ρ) = ρ := by
  set D := sylvesterCoeff r s t (Uᴴ * W) with hD
  set S : Matrix n n ℂ := diagonal (fun j => (s j : ℂ)) with hS
  set R : Matrix n n ℂ := diagonal (fun k => (r k : ℂ)) with hR
  have h1 : σ * (U * D * Wᴴ) = U * (S * D) * Wᴴ := by
    rw [hσe]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have h2 : U * D * Wᴴ * ρ = U * (D * R) * Wᴴ := by
    rw [hρe]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
  have h3 : U * ((Uᴴ * W) * R) * Wᴴ = ρ := by
    rw [hρe]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul]
  have h4 : (t : ℂ) • (U * (D * R) * Wᴴ) = U * ((t : ℂ) • (D * R)) * Wᴴ := by
    simp
  rw [h1, h2, h4, ← Matrix.add_mul, ← Matrix.mul_add, hD, sylvester_solve r s t (Uᴴ * W) hne, h3]


theorem trace_spectral {ρ : Matrix n n ℂ} {t : ℝ} (U W : Matrix n n ℂ) (r s : n → ℝ)
    (hW : Wᴴ * W = 1)
    (hρe : ρ = W * diagonal (fun k => (r k : ℂ)) * Wᴴ) :
    Matrix.trace (ρ * (U * sylvesterCoeff r s t (Uᴴ * W) * Wᴴ))
      = ((∑ k, ∑ j, (r k) ^ 2 * ‖(Uᴴ * W) j k‖ ^ 2 / (s j + t * r k) : ℝ) : ℂ) := by
  set C := Uᴴ * W with hC
  set D := sylvesterCoeff r s t C with hD
  set R : Matrix n n ℂ := diagonal (fun k => (r k : ℂ)) with hR
  have hWU : Wᴴ * U = Cᴴ := by rw [hC]; simp [Matrix.conjTranspose_mul]
  have step1 : Matrix.trace (ρ * (U * D * Wᴴ)) = Matrix.trace (R * Cᴴ * D) := by
    rw [hρe]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm W (R * (Wᴴ * (U * (D * Wᴴ))))]
    simp only [Matrix.mul_assoc, hW, Matrix.mul_one]
    rw [← Matrix.mul_assoc Wᴴ U D, hWU]
  rw [step1]
  rw [Matrix.trace]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hR, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hD, sylvesterCoeff, Matrix.of_apply]
  have hz : star (C j k) * C j k = ((‖C j k‖ : ℂ)) ^ 2 := by
    have h := RCLike.conj_mul (K := ℂ) (C j k)
    simpa [Complex.star_def] using h
  push_cast
  linear_combination ((r k : ℂ) * ((r k : ℂ) / ((s j : ℂ) + (t : ℂ) * (r k : ℂ)))) * hz


/-- The stationary point of `energy ρ σ t`, written in the eigenbases of `σ` and `ρ`. -/
noncomputable def statPoint (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (t : ℝ) : Matrix n n ℂ :=
  (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
    sylvesterCoeff hρ.isHermitian.eigenvalues hσ.isHermitian.eigenvalues t
      ((hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) *
    (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ

theorem eigen_denom_ne_zero (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (ht : 0 ≤ t) (j k : n) :
    hσ.isHermitian.eigenvalues j + t * hρ.isHermitian.eigenvalues k ≠ 0 := by
  have h1 : 0 < hσ.isHermitian.eigenvalues j := hσ.eigenvalues_pos j
  have h2 : 0 ≤ hρ.isHermitian.eigenvalues k := hρ.eigenvalues_nonneg k
  positivity

theorem statPoint_spec (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (ht : 0 ≤ t) :
    σ * statPoint hρ hσ t + (t : ℂ) • (statPoint hρ hσ t * ρ) = ρ :=
  stationary_of_spectral _ _ _ _
    (unitary_conjTranspose_mul_self hσ.isHermitian.eigenvectorUnitary)
    (unitary_mul_conjTranspose_self hσ.isHermitian.eigenvectorUnitary)
    (unitary_conjTranspose_mul_self hρ.isHermitian.eigenvectorUnitary)
    (IsHermitian.spectral_eq hσ.isHermitian) (IsHermitian.spectral_eq hρ.isHermitian)
    (eigen_denom_ne_zero hρ hσ ht)

theorem trace_mul_statPoint (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    (Matrix.trace (ρ * statPoint hρ hσ t)).re =
      ∑ k, ∑ j, (hρ.isHermitian.eigenvalues k) ^ 2 *
        eigenOverlap hρ.isHermitian hσ.isHermitian j k /
        (hσ.isHermitian.eigenvalues j + t * hρ.isHermitian.eigenvalues k) := by
  simp only [eigenOverlap]
  rw [statPoint, trace_spectral _ _ _ _
    (unitary_conjTranspose_mul_self hρ.isHermitian.eigenvectorUnitary)
    (IsHermitian.spectral_eq hρ.isHermitian), Complex.ofReal_re]

/-- The spectral formula for `Gfun`. -/
theorem Gfun_spectral (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (ht : 0 ≤ t) :
    Gfun ρ σ t =
      ∑ k, ∑ j, (hρ.isHermitian.eigenvalues k) ^ 2 *
        eigenOverlap hρ.isHermitian hσ.isHermitian j k /
        (hσ.isHermitian.eigenvalues j + t * hρ.isHermitian.eigenvalues k) := by
  rw [Gfun_eq_of_stationary hρ hσ.posSemidef ht (statPoint_spec hρ hσ ht),
    trace_mul_statPoint hρ hσ]

theorem bddAbove_energy (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (ht : 0 ≤ t) :
    BddAbove (Set.range (energy ρ σ t)) :=
  (isGreatest_energy hρ hσ.posSemidef ht (statPoint_spec hρ hσ ht)).bddAbove

end Spectral

/-! ### Monotonicity of `G` under channels -/

section Mono

variable {ρ σ : Matrix n n ℂ} {t : ℝ} {K : ι → Matrix m n ℂ}

omit [Fintype n] [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
theorem krausDual_conjTranspose (K : ι → Matrix m n ℂ) (X : Matrix m m ℂ) :
    (krausDual K X)ᴴ = krausDual K Xᴴ := by
  simp [krausDual, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem energy_krausMap_le (hK : IsTracePreserving K) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (ht : 0 ≤ t) (X : Matrix m m ℂ) :
    energy (krausMap K ρ) (krausMap K σ) t X ≤ energy ρ σ t (krausDual K X) := by
  have hlin : Matrix.trace (krausMap K ρ * X) = Matrix.trace (ρ * krausDual K X) := by
    rw [Matrix.trace_mul_comm (krausMap K ρ) X, ← trace_krausDual_mul K X ρ,
      Matrix.trace_mul_comm]
  have h2 : (Matrix.trace ((krausDual K X)ᴴ * krausDual K X * ρ)).re
      ≤ (Matrix.trace (Xᴴ * X * krausMap K ρ)).re := by
    have hmono := trace_mul_re_mono (kadison_schwarz hK X) hρ
    rw [trace_krausDual_mul K (Xᴴ * X) ρ] at hmono
    exact hmono
  have h1 : (Matrix.trace ((krausDual K X)ᴴ * σ * krausDual K X)).re
      ≤ (Matrix.trace (Xᴴ * krausMap K σ * X)).re := by
    have hks := kadison_schwarz hK Xᴴ
    simp only [krausDual_conjTranspose, Matrix.conjTranspose_conjTranspose] at hks
    have hmono := trace_mul_re_mono hks hσ
    rw [trace_krausDual_mul K (X * Xᴴ) σ] at hmono
    have e1 : Matrix.trace ((krausDual K X)ᴴ * σ * krausDual K X)
        = Matrix.trace (krausDual K X * (krausDual K X)ᴴ * σ) := by
      rw [Matrix.trace_mul_comm ((krausDual K X)ᴴ * σ) (krausDual K X), ← Matrix.mul_assoc]
    have e2 : Matrix.trace (X * Xᴴ * krausMap K σ) = Matrix.trace (Xᴴ * krausMap K σ * X) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [e1, ← e2, krausDual_conjTranspose]
    exact hmono
  simp only [energy, hlin]
  have := mul_le_mul_of_nonneg_left h2 ht
  linarith [h1, this]

theorem Gfun_krausMap_le (hK : IsTracePreserving K) (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (ht : 0 ≤ t) :
    Gfun (krausMap K ρ) (krausMap K σ) t ≤ Gfun ρ σ t := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨X, rfl⟩
  refine le_trans (energy_krausMap_le hK hρ hσ.posSemidef ht X) ?_
  exact le_csSup (bddAbove_energy hρ hσ ht) ⟨krausDual K X, rfl⟩

end Mono

end QI

import RequestProject.QI.Variational

/-!
# Spectral formula for the relative entropy

`relEntropy ρ σ` is expressed through the eigenvalues of `ρ` and `σ` and the overlap matrix
of their eigenbases.  This is the classical relative entropy of the Nussbaum–Szkoła
distributions attached to the pair `(ρ, σ)`.
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of a product of two matrices given by their spectral decompositions. -/
theorem trace_mul_spectral (U W : Matrix n n ℂ) (r g : n → ℝ) :
    Matrix.trace ((W * diagonal (fun k => (r k : ℂ)) * Wᴴ) *
        (U * diagonal (fun j => (g j : ℂ)) * Uᴴ))
      = ((∑ k, ∑ j, ‖(Uᴴ * W) j k‖ ^ 2 * (r k * g j) : ℝ) : ℂ) := by
  have step : Matrix.trace ((W * diagonal (fun k => (r k : ℂ)) * Wᴴ) *
      (U * diagonal (fun j => (g j : ℂ)) * Uᴴ))
      = Matrix.trace (diagonal (fun k => (r k : ℂ)) *
          ((Uᴴ * W)ᴴ * (diagonal (fun j => (g j : ℂ)) * (Uᴴ * W)))) := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm W (diagonal (fun k => (r k : ℂ)) *
      (Wᴴ * (U * (diagonal (fun j => (g j : ℂ)) * Uᴴ))))]
    simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [step, Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_apply, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_mul]
  have hz : star ((Uᴴ * W) j k) * ((Uᴴ * W) j k) = ((‖(Uᴴ * W) j k‖ : ℂ)) ^ 2 := by
    have h := RCLike.conj_mul (K := ℂ) ((Uᴴ * W) j k)
    simpa [Complex.star_def] using h
  push_cast
  linear_combination ((r k : ℂ) * (g j : ℂ)) * hz

theorem trace_mul_cfc_log (U W : Matrix n n ℂ) (r g : n → ℝ)
    {ρ σ : Matrix n n ℂ} (hρe : ρ = W * diagonal (fun k => (r k : ℂ)) * Wᴴ)
    (hσe : σ = U * diagonal (fun j => (g j : ℂ)) * Uᴴ) :
    Matrix.trace (ρ * σ) = ((∑ k, ∑ j, ‖(Uᴴ * W) j k‖ ^ 2 * (r k * g j) : ℝ) : ℂ) := by
  rw [hρe, hσe, trace_mul_spectral U W r g]

/-- `Tr (ρ log ρ)` in terms of the eigenvalues of `ρ`. -/
theorem trace_mul_cfc_log_self {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    Matrix.trace (ρ * cfc Real.log ρ)
      = ((∑ k, hρ.eigenvalues k * Real.log (hρ.eigenvalues k) : ℝ) : ℂ) := by
  have hW := unitary_conjTranspose_mul_self hρ.eigenvectorUnitary
  rw [trace_mul_cfc_log (hρ.eigenvectorUnitary : Matrix n n ℂ)
    (hρ.eigenvectorUnitary : Matrix n n ℂ) hρ.eigenvalues (fun k => Real.log (hρ.eigenvalues k))
    (IsHermitian.spectral_eq hρ) (IsHermitian.cfc_eq' hρ Real.log)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hW]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- `Tr (ρ log σ)` in terms of the spectral data of `ρ` and `σ`. -/
theorem trace_mul_cfc_log_other {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Matrix.trace (ρ * cfc Real.log σ)
      = ((∑ k, ∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
            (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2 *
          (hρ.eigenvalues k * Real.log (hσ.eigenvalues j)) : ℝ) : ℂ) :=
  trace_mul_cfc_log _ _ _ _
    (IsHermitian.spectral_eq hρ) (IsHermitian.cfc_eq' hσ Real.log)

/-- The columns of a matrix with orthonormal columns have unit norm. -/
theorem sum_norm_sq_col (C : Matrix n n ℂ) (hC : Cᴴ * C = 1) (k : n) :
    ∑ j, ‖C j k‖ ^ 2 = 1 := by
  have h2 := congrArg (fun M : Matrix n n ℂ => M k k) hC
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h2
  have h3 : ∀ j : n, star (C j k) * C j k = ((‖C j k‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have h := RCLike.conj_mul (K := ℂ) (C j k)
    push_cast
    simpa [Complex.star_def] using h
  simp only [h3, ← Complex.ofReal_sum] at h2
  exact_mod_cast h2

/-- The overlap matrix of the two eigenbases is unitary. -/
theorem eigen_overlap_isometry {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hρ.eigenvectorUnitary : Matrix n n ℂ))ᴴ *
      ((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hρ.eigenvectorUnitary : Matrix n n ℂ)) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (hσ.eigenvectorUnitary : Matrix n n ℂ)
      ((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ),
    unitary_mul_conjTranspose_self hσ.eigenvectorUnitary, Matrix.one_mul,
    unitary_conjTranspose_mul_self hρ.eigenvectorUnitary]

/-- Each column of the overlap matrix is a probability vector. -/
theorem sum_eigenOverlap {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (k : n) :
    ∑ j, eigenOverlap hρ hσ j k = 1 :=
  sum_norm_sq_col _ (eigen_overlap_isometry hρ hσ) k

/-- The spectral (Nussbaum–Szkoła) formula for the relative entropy. -/
theorem relEntropy_spectral {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ρ σ =
      ∑ k, ∑ j, eigenOverlap hρ hσ j k *
        (hρ.eigenvalues k * Real.log (hρ.eigenvalues k) -
          hρ.eigenvalues k * Real.log (hσ.eigenvalues j)) := by
  simp only [eigenOverlap]
  have hcol := fun k => sum_norm_sq_col _ (eigen_overlap_isometry hρ hσ) k
  rw [relEntropy, trace_mul_cfc_log_self hρ, trace_mul_cfc_log_other hρ hσ,
    ← Complex.ofReal_sub, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2 *
        (hρ.eigenvalues k * Real.log (hρ.eigenvalues k) -
          hρ.eigenvalues k * Real.log (hσ.eigenvalues j))
      = (∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2) *
          (hρ.eigenvalues k * Real.log (hρ.eigenvalues k)) -
        ∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2 *
          (hρ.eigenvalues k * Real.log (hσ.eigenvalues j)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, hcol k, one_mul]

end QI

import RequestProject.QI.Entropy
import RequestProject.QI.ScalarIntegral

/-!
# Integral representation of the relative entropy

`relEntropy ρ σ = ∫_0^∞ (Gfun ρ σ t - (Tr ρ) / (1 + t)) dt` for `ρ` positive semidefinite and
`σ` positive definite.
-/

set_option maxHeartbeats 1000000

open Matrix MeasureTheory Filter Set
open scoped ComplexOrder MatrixOrder Topology

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}

/-- The `(k, j)` term of the integrand. -/
noncomputable def entropyIntegrand (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (k j : n) (t : ℝ) : ℝ :=
  eigenOverlap hρ.isHermitian hσ.isHermitian j k *
    ((hρ.isHermitian.eigenvalues k) ^ 2 /
        (hσ.isHermitian.eigenvalues j + t * hρ.isHermitian.eigenvalues k) -
      hρ.isHermitian.eigenvalues k / (1 + t))

theorem trace_re_eq_sum_eigenvalues (hρ : ρ.PosSemidef) :
    (Matrix.trace ρ).re = ∑ k, hρ.isHermitian.eigenvalues k := by
  rw [hρ.isHermitian.trace_eq_sum_eigenvalues]
  simp

/-- Pointwise decomposition of the integrand. -/
theorem Gfun_sub_eq_sum (hρ : ρ.PosSemidef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    Gfun ρ σ t - (Matrix.trace ρ).re / (1 + t)
      = ∑ k, ∑ j, entropyIntegrand hρ hσ k j t := by
  rw [Gfun_spectral hρ hσ ht, trace_re_eq_sum_eigenvalues hρ, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∑ j, entropyIntegrand hρ hσ k j t
      = (∑ j, eigenOverlap hρ.isHermitian hσ.isHermitian j k *
          ((hρ.isHermitian.eigenvalues k) ^ 2 /
            (hσ.isHermitian.eigenvalues j + t * hρ.isHermitian.eigenvalues k))) -
        (∑ j, eigenOverlap hρ.isHermitian hσ.isHermitian j k) *
          (hρ.isHermitian.eigenvalues k / (1 + t)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [entropyIntegrand]; ring
  rw [e, sum_eigenOverlap hρ.isHermitian hσ.isHermitian k, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem integrable_entropyIntegrand (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (k j : n) :
    IntegrableOn (entropyIntegrand hρ hσ k j) (Ioi 0) :=
  (integrableOn_entropyTerm (hρ.eigenvalues_nonneg k) (hσ.eigenvalues_pos j)).const_mul _

theorem integral_entropyIntegrand (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (k j : n) :
    ∫ t in Ioi (0 : ℝ), entropyIntegrand hρ hσ k j t
      = eigenOverlap hρ.isHermitian hσ.isHermitian j k *
        (hρ.isHermitian.eigenvalues k * Real.log (hρ.isHermitian.eigenvalues k) -
          hρ.isHermitian.eigenvalues k * Real.log (hσ.isHermitian.eigenvalues j)) := by
  simp only [entropyIntegrand]
  rw [integral_const_mul,
    integral_entropyTerm (hρ.eigenvalues_nonneg k) (hσ.eigenvalues_pos j)]

theorem integrableOn_Gfun_sub (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    IntegrableOn (fun t => Gfun ρ σ t - (Matrix.trace ρ).re / (1 + t)) (Ioi 0) := by
  have hsum : IntegrableOn (fun t => ∑ k, ∑ j, entropyIntegrand hρ hσ k j t) (Ioi 0) := by
    refine integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => ?_
    exact integrable_entropyIntegrand hρ hσ k j
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact (Gfun_sub_eq_sum hρ hσ (le_of_lt ht)).symm

/-- The integral representation of the quantum relative entropy. -/
theorem relEntropy_eq_integral (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    relEntropy ρ σ = ∫ t in Ioi (0 : ℝ), (Gfun ρ σ t - (Matrix.trace ρ).re / (1 + t)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => Gfun_sub_eq_sum hρ hσ (le_of_lt (mem_Ioi.mp ht)))]
  rw [integral_finset_sum _ fun k _ =>
    integrable_finset_sum _ fun j _ => integrable_entropyIntegrand hρ hσ k j]
  rw [relEntropy_spectral hρ.isHermitian hσ.isHermitian]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun j _ => integrable_entropyIntegrand hρ hσ k j]
  exact Finset.sum_congr rfl fun j _ => (integral_entropyIntegrand hρ hσ k j).symm

end QI

import RequestProject.QI.Defs

/-!
# The Kadison–Schwarz inequality for Kraus channels

For a trace preserving family of Kraus operators `K`, the adjoint map
`krausDual K` is unital and completely positive, and satisfies
`(krausDual K X)ᴴ * (krausDual K X) ≤ krausDual K (Xᴴ * X)`.

The proof stacks the Kraus operators into a single isometry `R`, writes
`krausDual K X = Rᴴ * Y * R` with `Y` block diagonal, and uses that
`1 - R * Rᴴ` is an orthogonal projection.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- Kadison–Schwarz inequality for a conjugation by an isometry. -/
theorem kadison_schwarz_isometry {p : Type*} [Fintype p] [DecidableEq p]
    (R : Matrix p n ℂ) (hR : Rᴴ * R = 1) (Y : Matrix p p ℂ) :
    ((Rᴴ * (Yᴴ * Y) * R) - (Rᴴ * Y * R)ᴴ * (Rᴴ * Y * R)).PosSemidef := by
  have hP : ((1 : Matrix p p ℂ) - R * Rᴴ).PosSemidef := by
    have hid : ((1 : Matrix p p ℂ) - R * Rᴴ)ᴴ * ((1 : Matrix p p ℂ) - R * Rᴴ)
        = (1 : Matrix p p ℂ) - R * Rᴴ := by
      have : (R * Rᴴ) * (R * Rᴴ) = R * Rᴴ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R Rᴴ, hR, Matrix.one_mul]
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, this]
      abel
    rw [← hid]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have key : (Rᴴ * (Yᴴ * Y) * R) - (Rᴴ * Y * R)ᴴ * (Rᴴ * Y * R)
      = (Y * R)ᴴ * ((1 : Matrix p p ℂ) - R * Rᴴ) * (Y * R) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [key]
  exact hP.conjTranspose_mul_mul_same _

/-- The stacked Kraus operators, an isometry when the channel is trace preserving. -/
noncomputable def krausStack (K : ι → Matrix m n ℂ) : Matrix (m × ι) n ℂ :=
  Matrix.of fun p b => K p.2 p.1 b

omit [Fintype n] [DecidableEq m] [DecidableEq ι] in
theorem krausStack_isometry {K : ι → Matrix m n ℂ} (hK : IsTracePreserving K) :
    (krausStack K)ᴴ * (krausStack K) = 1 := by
  ext b c
  have : ((krausStack K)ᴴ * krausStack K) b c = ∑ i, ((K i)ᴴ * K i) b c := by
    simp [krausStack, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Finset.sum_comm (γ := ι)]
  rw [this, ← Matrix.sum_apply, hK]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem krausDual_eq_stack (K : ι → Matrix m n ℂ) (X : Matrix m m ℂ) :
    krausDual K X = (krausStack K)ᴴ * (Matrix.blockDiagonal fun _ : ι => X) * (krausStack K) := by
  ext b c
  simp only [krausDual, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    krausStack, Matrix.of_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type,
    Finset.sum_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

/-- **Kadison–Schwarz inequality** for the adjoint of a trace preserving Kraus channel. -/
theorem kadison_schwarz {K : ι → Matrix m n ℂ} (hK : IsTracePreserving K) (X : Matrix m m ℂ) :
    (krausDual K (Xᴴ * X) - (krausDual K X)ᴴ * (krausDual K X)).PosSemidef := by
  have h1 := kadison_schwarz_isometry (krausStack K) (krausStack_isometry hK)
    (Matrix.blockDiagonal fun _ : ι => X)
  rw [← krausDual_eq_stack K X] at h1
  have h2 : (Matrix.blockDiagonal fun _ : ι => X)ᴴ * (Matrix.blockDiagonal fun _ : ι => X)
      = Matrix.blockDiagonal fun _ : ι => Xᴴ * X := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  rw [h2, ← krausDual_eq_stack K (Xᴴ * X)] at h1
  exact h1

end QI

import Mathlib

/-!
# Basic definitions for the quantum data-processing inequality

We work with finite dimensional quantum systems, described by complex matrices.

* `QI.relEntropy ρ σ` is the Umegaki quantum relative entropy `Tr ρ (log ρ - log σ)`,
  where the matrix logarithm is the continuous functional calculus applied to `Real.log`.
* `QI.krausMap K` is the quantum channel with Kraus operators `K`,
  and `QI.krausDual K` is its adjoint (Heisenberg picture) map.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- The Umegaki quantum relative entropy `Tr ρ (log ρ - log σ)`. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * cfc Real.log ρ) - Matrix.trace (ρ * cfc Real.log σ)).re

/-- The quantum channel (Schrödinger picture) with Kraus operators `K`. -/
noncomputable def krausMap (K : ι → Matrix m n ℂ) (A : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i, K i * A * (K i)ᴴ

/-- The adjoint (Heisenberg picture) map of the channel with Kraus operators `K`. -/
noncomputable def krausDual (K : ι → Matrix m n ℂ) (B : Matrix m m ℂ) : Matrix n n ℂ :=
  ∑ i, (K i)ᴴ * B * K i

/-- Trace preservation of the channel with Kraus operators `K`. -/
def IsTracePreserving (K : ι → Matrix m n ℂ) : Prop := ∑ i, (K i)ᴴ * K i = 1

/-! ### Spectral decompositions -/

theorem IsHermitian.spectral_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]

theorem IsHermitian.cfc_eq' {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  rw [hA.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def,
    Matrix.star_eq_conjTranspose]

theorem unitary_conjTranspose_mul_self (U : Matrix.unitaryGroup n ℂ) :
    (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    (Unitary.star_mul_self_of_mem (U.2) : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1)

theorem unitary_mul_conjTranspose_self (U : Matrix.unitaryGroup n ℂ) :
    (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    (Unitary.mul_star_self_of_mem (U.2) : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1)

/-- The overlap weights `|⟨u_j, w_k⟩|²` between the eigenbasis of `σ` (vectors `u_j`) and the
eigenbasis of `ρ` (vectors `w_k`). -/
noncomputable def eigenOverlap {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (j k : n) : ℝ :=
  ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2

/-! ### Traces and positivity -/

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_re_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A (ha := hA.nonneg)
  have hsq : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have h1 : Matrix.trace (A * B) = Matrix.trace (CFC.sqrt A * B * CFC.sqrt A) := by
    conv_lhs => rw [← hs]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    have := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
    rwa [hsq.isHermitian.eq] at this
  rw [h1]
  exact (Complex.le_def.mp h2.trace_nonneg).1

/-- Monotonicity of `A ↦ Tr (A B)` in `A` for `B` positive semidefinite. -/
theorem trace_mul_re_mono {A A' B : Matrix n n ℂ} (h : (A' - A).PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace (A * B)).re ≤ (Matrix.trace (A' * B)).re := by
  have := trace_mul_re_nonneg h hB
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

omit [DecidableEq n] [DecidableEq m] in
theorem krausMap_posSemidef {K : ι → Matrix m n ℂ} {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (krausMap K A).PosSemidef := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro i _
  simpa using hA.mul_mul_conjTranspose_same (K i)

omit [DecidableEq n] [DecidableEq m] in
theorem krausDual_posSemidef {K : ι → Matrix m n ℂ} {B : Matrix m m ℂ} (hB : B.PosSemidef) :
    (krausDual K B).PosSemidef := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro i _
  simpa using hB.conjTranspose_mul_mul_same (K i)

omit [DecidableEq m] in
theorem krausMap_trace {K : ι → Matrix m n ℂ} (hK : IsTracePreserving K) (A : Matrix n n ℂ) :
    Matrix.trace (krausMap K A) = Matrix.trace A := by
  simp only [krausMap, Matrix.trace_sum]
  rw [show (∑ i, Matrix.trace (K i * A * (K i)ᴴ)) = ∑ i, Matrix.trace ((K i)ᴴ * K i * A) from
    Finset.sum_congr rfl fun i _ => by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

omit [DecidableEq n] [DecidableEq m] in
/-- Duality between the channel and its adjoint. -/
theorem trace_krausDual_mul (K : ι → Matrix m n ℂ) (B : Matrix m m ℂ) (A : Matrix n n ℂ) :
    Matrix.trace (krausDual K B * A) = Matrix.trace (B * krausMap K A) := by
  simp only [krausDual, krausMap, Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_mul_comm ((K i)ᴴ * B * K i) A, Matrix.trace_mul_comm B (K i * A * (K i)ᴴ)]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (A * (K i)ᴴ * B) (K i), ← Matrix.mul_assoc, ← Matrix.mul_assoc]

end QI

import Mathlib

/-!
# The scalar integral behind the integral representation of the relative entropy

For `r ≥ 0` and `s > 0`,
`∫_0^∞ (r² / (s + t r) - r / (1 + t)) dt = r log r - r log s`.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace QI

/-- The antiderivative of `t ↦ r² / (s + t r) - r / (1 + t)`. -/
noncomputable def logAnti (r s t : ℝ) : ℝ := r * Real.log (s + t * r) - r * Real.log (1 + t)

theorem hasDerivAt_logAnti {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (logAnti r s) (r ^ 2 / (s + t * r) - r / (1 + t)) t := by
  have h1 : (0 : ℝ) < s + t * r := by positivity
  have h2 : (0 : ℝ) < 1 + t := by linarith
  have d1 : HasDerivAt (fun u : ℝ => s + u * r) r t := by
    simpa using ((hasDerivAt_id t).mul_const r).const_add s
  have d2 : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have e1 : HasDerivAt (fun u : ℝ => Real.log (s + u * r)) (r / (s + t * r)) t := d1.log h1.ne'
  have e2 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := d2.log h2.ne'
  have := (e1.const_mul r).sub (e2.const_mul r)
  convert this using 1
  field_simp

theorem tendsto_logAnti {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (logAnti r s) atTop (𝓝 (r * Real.log r)) := by
  have hden : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have h0 : Tendsto (fun t : ℝ => (s - r) / (1 + t)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  have h1 : Tendsto (fun t : ℝ => r + (s - r) / (1 + t)) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add h0
  have h2 : Tendsto (fun t : ℝ => Real.log (r + (s - r) / (1 + t))) atTop (𝓝 (Real.log r)) :=
    (Real.continuousAt_log hr.ne').tendsto.comp h1
  have h3 : Tendsto (fun t : ℝ => r * Real.log (r + (s - r) / (1 + t))) atTop
      (𝓝 (r * Real.log r)) := h2.const_mul r
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h4 : (0 : ℝ) < s + t * r := by positivity
  have h5 : (0 : ℝ) < 1 + t := by linarith
  have h6 : r + (s - r) / (1 + t) = (s + t * r) / (1 + t) := by
    field_simp
    ring
  rw [h6, Real.log_div h4.ne' h5.ne', logAnti]
  ring

theorem integrableOn_entropyTerm {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    IntegrableOn (fun t => r ^ 2 / (s + t * r) - r / (1 + t)) (Ioi 0) := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · simp [← hr0]
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (logAnti r s)
      (r ^ 2 / (s + t * r) - r / (1 + t)) t := fun t ht => hasDerivAt_logAnti hr0 hs ht
  rcases le_total s r with hrs | hrs
  · refine integrableOn_Ioi_deriv_of_nonneg' hderiv (fun t ht => ?_) (tendsto_logAnti hr0 hs)
    have ht0 : (0 : ℝ) < t := ht
    have h1 : (0 : ℝ) < s + t * r := by positivity
    have h2 : (0 : ℝ) < 1 + t := by linarith
    rw [sub_nonneg, div_le_div_iff₀ h2 h1]
    nlinarith
  · refine integrableOn_Ioi_deriv_of_nonpos' hderiv (fun t ht => ?_) (tendsto_logAnti hr0 hs)
    have ht0 : (0 : ℝ) < t := ht
    have h1 : (0 : ℝ) < s + t * r := by positivity
    have h2 : (0 : ℝ) < 1 + t := by linarith
    rw [sub_nonpos, div_le_div_iff₀ h1 h2]
    nlinarith

theorem integral_entropyTerm {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), (r ^ 2 / (s + t * r) - r / (1 + t))
      = r * Real.log r - r * Real.log s := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · simp [← hr0]
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (logAnti r s)
      (r ^ 2 / (s + t * r) - r / (1 + t)) t := fun t ht => hasDerivAt_logAnti hr0 hs ht
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_entropyTerm hr hs)
    (tendsto_logAnti hr0 hs)]
  simp [logAnti]

end QI

/-
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Statement: Quantum relative entropy is monotone under CPTP maps (data-processing inequality).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.QI.IntegralFormula

/-!
The data-processing inequality for the Umegaki relative entropy

`relEntropy ρ σ = Re Tr (ρ log ρ - ρ log σ)`

of matrices, with respect to a completely positive trace-preserving map given in Kraus form
`krausMap K A = ∑ i, K i * A * (K i)ᴴ` with `∑ i, (K i)ᴴ * (K i) = 1`.

(The header comment at the top of this file uses plain block-comment delimiters rather than
module-docstring delimiters, since Lean requires `import` commands to precede any doc comment.)
-/

set_option maxHeartbeats 1000000

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder

namespace QI

/-- **Data-processing inequality.** The Umegaki relative entropy of two states is
non-increasing under a completely positive trace-preserving map, presented in Kraus form
`Φ(A) = ∑ i, K i * A * (K i)ᴴ` with `∑ i, (K i)ᴴ * (K i) = 1`.

Here `ρ` is positive semidefinite and `σ` is positive definite; the image `Φ σ` is assumed
positive definite as well, which is the usual non-degeneracy condition making both sides finite
(a channel may map a full-rank `σ` to a singular matrix, in which case the left-hand relative
entropy is `+∞` informally and the `Real.log 0 = 0` convention used here would not represent it). -/
theorem data_processing {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype ι] {K : ι → Matrix m n ℂ} (hK : IsTracePreserving K)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hσ' : (krausMap K σ).PosDef) :
    relEntropy (krausMap K ρ) (krausMap K σ) ≤ relEntropy ρ σ := by
  classical
  rw [relEntropy_eq_integral (krausMap_posSemidef hρ) hσ',
    relEntropy_eq_integral hρ hσ]
  have htr : (Matrix.trace (krausMap K ρ)).re = (Matrix.trace ρ).re := by
    rw [krausMap_trace hK]
  refine setIntegral_mono_on
    (integrableOn_Gfun_sub (krausMap_posSemidef hρ) hσ')
    (integrableOn_Gfun_sub hρ hσ) measurableSet_Ioi ?_
  intro t ht
  rw [htr]
  exact sub_le_sub_right (Gfun_krausMap_le hK hρ hσ (le_of_lt (mem_Ioi.mp ht))) _

end QI

