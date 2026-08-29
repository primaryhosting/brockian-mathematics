import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
mandated header block is placed immediately after the single `import Mathlib` line.

## Overview

This file formalises the Coffman–Kundu–Wootters (CKW) monogamy inequality for three qubits:
for a pure state `ψ` of three qubits,

  `τ(A|B) + τ(A|C) ≤ τ(A|BC)`,

where `τ = C²` is the tangle (squared concurrence).

The development is self-contained.  A pure three-qubit state is recorded by its amplitude
array `ψ : Fin 2 → Fin 2 → Fin 2 → ℂ`.

*  `QI.rhoA ψ` is the one-qubit reduced density matrix on `A`, and
   `QI.tangleABC ψ = 4 · det (ρ_A)` is the tangle of the bipartition `A|BC`
   (`C²_{A|BC} = 2(1 - tr ρ_A²) = 4 det ρ_A` for a `2 × 2` density matrix).

*  The two-qubit reduced state `ρ_AB = tr_C |ψ⟩⟨ψ|` has rank at most two: it is
   `|u₀⟩⟨u₀| + |u₁⟩⟨u₁|` with `(u_k)_{ij} = ψ i j k`.  Writing `Y = σ_y ⊗ σ_y` and
   `S_{kl} = u_kᵀ Y u_l`, the nonzero spectrum of `ρ_AB ρ̃_AB` (with `ρ̃ = Y ρ* Y` the
   spin flip) coincides with the spectrum of `S̄ S`, i.e. with the squared singular values
   `σ₁², σ₂²` of the symmetric matrix `S`.  Wootters' formula for a rank-two state therefore
   gives `C_AB = σ₁ - σ₂`, hence
     `τ_AB = C²_AB = σ₁² + σ₂² - 2σ₁σ₂ = ‖S‖²_F - 2|det S|`,
   using `σ₁² + σ₂² = ‖S‖²_F` and `σ₁σ₂ = |det S|`.  This closed formula is taken as the
   definition of `QI.tangleAB` (and symmetrically `QI.tangleAC`); it is well posed because
   `‖S‖²_F ≥ 2|det S|` always (`QI.two_norm_det_le_frob`).

*  The heart of the proof is the polynomial identity (`QI.four_det_rhoA_eq`)
     `4 · det ρ_A = ‖S_AB‖²_F + ‖S_AC‖²_F`,
   from which CKW is immediate, and which refines to the exact CKW identity
     `τ_{A|BC} = τ_AB + τ_AC + τ_ABC`
   with residual three-tangle `τ_ABC = 2|det S_AB| + 2|det S_AC| = 4 |Det ψ|`,
   `Det` being Cayley's hyperdeterminant (`QI.det_SAB_eq_neg_cayley`).
-/

open scoped BigOperators

namespace QI

/-- Amplitude array of a pure state of three qubits: `ψ i j k` is the coefficient of
`|i⟩ ⊗ |j⟩ ⊗ |k⟩`. -/
abbrev QState := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- Normalisation of a three-qubit amplitude array. -/
def IsNormalized (psi : QState) : Prop :=
  ∑ i, ∑ j, ∑ k, Complex.normSq (psi i j k) = 1

/-- The reduced density matrix of qubit `A`, i.e. `tr_{BC} |ψ⟩⟨ψ|`. -/
noncomputable def rhoA (psi : QState) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j, ∑ k, psi i j k * (starRingEnd ℂ) (psi i' j k)

/-- The `2 × 2` complex symmetric matrix `S_{kl} = u_kᵀ (σ_y ⊗ σ_y) u_l`, where
`(u_k)_{ij} = ψ i j k`, so that `ρ_AB = ∑_k |u_k⟩⟨u_k|`.  Its singular values are the
Wootters eigenvalues of `ρ_AB`. -/
def SAB (psi : QState) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun k l =>
    -(psi 0 0 k * psi 1 1 l + psi 1 1 k * psi 0 0 l
      - psi 0 1 k * psi 1 0 l - psi 1 0 k * psi 0 1 l)

/-- The analogue of `QI.SAB` for the pair `A C`: `T_{jj'} = v_jᵀ (σ_y ⊗ σ_y) v_{j'}` with
`(v_j)_{ik} = ψ i j k`. -/
def SAC (psi : QState) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j j' =>
    -(psi 0 j 0 * psi 1 j' 1 + psi 1 j 1 * psi 0 j' 0
      - psi 0 j 1 * psi 1 j' 0 - psi 1 j 0 * psi 0 j' 1)

/-- Squared Frobenius norm of a `2 × 2` complex matrix. -/
noncomputable def frob (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

lemma frob_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frob M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- For a `2 × 2` complex matrix, twice the modulus of the determinant (i.e. twice the
product of the singular values) is at most the squared Frobenius norm (the sum of the
squared singular values).  This is what makes the tangle formula below nonnegative. -/
theorem two_norm_det_le_frob (M : Matrix (Fin 2) (Fin 2) ℂ) :
    2 * ‖M.det‖ ≤ frob M := by
  have h1 : ‖M.det‖ ≤ ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by
    rw [Matrix.det_fin_two]
    calc ‖M 0 0 * M 1 1 - M 0 1 * M 1 0‖ ≤ ‖M 0 0 * M 1 1‖ + ‖M 0 1 * M 1 0‖ :=
          norm_sub_le _ _
      _ = ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by rw [norm_mul, norm_mul]
  have h2 : ∀ z w : ℂ, 2 * (‖z‖ * ‖w‖) ≤ Complex.normSq z + Complex.normSq w := by
    intro z w
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  have ha := h2 (M 0 0) (M 1 1)
  have hb := h2 (M 0 1) (M 1 0)
  simp only [frob, Fin.sum_univ_two]
  linarith

/-- The tangle of the bipartition `A | BC`, namely `C²_{A|BC} = 4 det ρ_A`. -/
noncomputable def tangleABC (psi : QState) : ℝ := 4 * (rhoA psi).det.re

/-- The tangle (squared concurrence) of the two-qubit reduced state `ρ_AB`,
via Wootters' formula in the rank-two closed form `‖S‖²_F - 2|det S|`. -/
noncomputable def tangleAB (psi : QState) : ℝ := frob (SAB psi) - 2 * ‖(SAB psi).det‖

/-- The tangle (squared concurrence) of the two-qubit reduced state `ρ_AC`. -/
noncomputable def tangleAC (psi : QState) : ℝ := frob (SAC psi) - 2 * ‖(SAC psi).det‖

/-- The residual (three-)tangle `τ_{ABC}`. -/
noncomputable def residualTangle (psi : QState) : ℝ :=
  2 * ‖(SAB psi).det‖ + 2 * ‖(SAC psi).det‖

/-- Concurrence of the bipartition `A|BC`. -/
noncomputable def concurrenceABC (psi : QState) : ℝ := Real.sqrt (tangleABC psi)

/-- Concurrence of the reduced state `ρ_AB`. -/
noncomputable def concurrenceAB (psi : QState) : ℝ := Real.sqrt (tangleAB psi)

/-- Concurrence of the reduced state `ρ_AC`. -/
noncomputable def concurrenceAC (psi : QState) : ℝ := Real.sqrt (tangleAC psi)

/-! ### The key algebraic identity -/

/-- The central identity: `4 det ρ_A = ‖S_AB‖²_F + ‖S_AC‖²_F`.  Both sides are homogeneous
of bidegree `(2,2)` in `ψ, ψ̄`, so no normalisation is required. -/
theorem four_det_rhoA_eq (psi : QState) :
    4 * (rhoA psi).det = ((frob (SAB psi) + frob (SAC psi) : ℝ) : ℂ) := by
  simp only [rhoA, SAB, SAC, frob, Matrix.det_fin_two, Matrix.of_apply, Fin.sum_univ_two,
    Complex.ofReal_add, ← Complex.mul_conj, map_add, map_sub, map_neg, map_mul]
  ring

/-- Real form of the key identity: `τ_{A|BC} = ‖S_AB‖²_F + ‖S_AC‖²_F`. -/
theorem tangleABC_eq_frob_add_frob (psi : QState) :
    tangleABC psi = frob (SAB psi) + frob (SAC psi) := by
  have h := four_det_rhoA_eq psi
  have := congrArg Complex.re h
  simpa [tangleABC] using this

/-! ### Nonnegativity -/

theorem tangleAB_nonneg (psi : QState) : 0 ≤ tangleAB psi := by
  have := two_norm_det_le_frob (SAB psi)
  simp only [tangleAB]; linarith

theorem tangleAC_nonneg (psi : QState) : 0 ≤ tangleAC psi := by
  have := two_norm_det_le_frob (SAC psi)
  simp only [tangleAC]; linarith

theorem residualTangle_nonneg (psi : QState) : 0 ≤ residualTangle psi := by
  have h1 : (0:ℝ) ≤ ‖(SAB psi).det‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖(SAC psi).det‖ := norm_nonneg _
  simp only [residualTangle]; linarith

theorem tangleABC_nonneg (psi : QState) : 0 ≤ tangleABC psi := by
  rw [tangleABC_eq_frob_add_frob]
  have := frob_nonneg (SAB psi)
  have := frob_nonneg (SAC psi)
  linarith

/-! ### The CKW identity and the monogamy inequality -/

/-- The exact CKW identity: the tangle of the bipartition `A|BC` splits as the sum of the
two pairwise tangles plus the (nonnegative) residual three-tangle. -/
theorem ckw_identity (psi : QState) :
    tangleABC psi = tangleAB psi + tangleAC psi + residualTangle psi := by
  rw [tangleABC_eq_frob_add_frob]
  simp only [tangleAB, tangleAC, residualTangle]
  ring

/-- **Coffman–Kundu–Wootters monogamy inequality.**  For every pure state of three qubits,
the tangles (squared concurrences) of the reduced two-qubit states `ρ_AB` and `ρ_AC` sum to
at most the tangle of the bipartition `A|BC`:
`C²_{AB} + C²_{AC} ≤ C²_{A|BC}`.  (Normalisation of `ψ` is not needed: all three quantities
are homogeneous of the same degree.) -/
theorem monogamy_ckw (psi : QState) :
    tangleAB psi + tangleAC psi ≤ tangleABC psi := by
  rw [ckw_identity]
  have := residualTangle_nonneg psi
  linarith

/-- The monogamy inequality phrased with concurrences. -/
theorem monogamy_ckw_concurrence (psi : QState) :
    concurrenceAB psi ^ 2 + concurrenceAC psi ^ 2 ≤ concurrenceABC psi ^ 2 := by
  rw [concurrenceAB, concurrenceAC, concurrenceABC,
    Real.sq_sqrt (tangleAB_nonneg psi), Real.sq_sqrt (tangleAC_nonneg psi),
    Real.sq_sqrt (tangleABC_nonneg psi)]
  exact monogamy_ckw psi

/-! ### Identification of the residual tangle with Cayley's hyperdeterminant -/

/-- Cayley's hyperdeterminant of a `2 × 2 × 2` array. -/
def cayleyHyperdet (psi : QState) : ℂ :=
  (psi 0 0 0)^2 * (psi 1 1 1)^2 + (psi 0 0 1)^2 * (psi 1 1 0)^2
    + (psi 0 1 0)^2 * (psi 1 0 1)^2 + (psi 1 0 0)^2 * (psi 0 1 1)^2
    - 2 * (psi 0 0 0 * psi 0 0 1 * psi 1 1 0 * psi 1 1 1
         + psi 0 0 0 * psi 0 1 0 * psi 1 0 1 * psi 1 1 1
         + psi 0 0 0 * psi 1 0 0 * psi 0 1 1 * psi 1 1 1
         + psi 0 0 1 * psi 0 1 0 * psi 1 0 1 * psi 1 1 0
         + psi 0 0 1 * psi 1 0 0 * psi 0 1 1 * psi 1 1 0
         + psi 0 1 0 * psi 1 0 0 * psi 0 1 1 * psi 1 0 1)
    + 4 * (psi 0 0 0 * psi 0 1 1 * psi 1 0 1 * psi 1 1 0
         + psi 0 0 1 * psi 0 1 0 * psi 1 0 0 * psi 1 1 1)

theorem det_SAB_eq_neg_cayley (psi : QState) :
    (SAB psi).det = -cayleyHyperdet psi := by
  simp only [SAB, cayleyHyperdet, Matrix.det_fin_two, Matrix.of_apply]
  ring

theorem det_SAC_eq_neg_cayley (psi : QState) :
    (SAC psi).det = -cayleyHyperdet psi := by
  simp only [SAC, cayleyHyperdet, Matrix.det_fin_two, Matrix.of_apply]
  ring

/-- The residual tangle equals `4 |Det ψ|`, four times the modulus of Cayley's
hyperdeterminant — the standard three-tangle. -/
theorem residualTangle_eq (psi : QState) :
    residualTangle psi = 4 * ‖cayleyHyperdet psi‖ := by
  simp only [residualTangle, det_SAB_eq_neg_cayley, det_SAC_eq_neg_cayley, norm_neg]
  ring

/-! ### Sanity checks: the GHZ and W states

These worked examples confirm that the definitions reproduce the textbook values
`τ_{A|BC} = 1, τ_AB = τ_AC = 0, τ_ABC = 1` for GHZ and
`τ_{A|BC} = 8/9, τ_AB = τ_AC = 4/9, τ_ABC = 0` for W. -/

/-- The GHZ family `t·(|000⟩ + |111⟩)`. -/
noncomputable def ghzState (t : ℂ) : QState :=
  ![![![t, 0], ![0, 0]], ![![0, 0], ![0, t]]]

/-- The W family `t·(|001⟩ + |010⟩ + |100⟩)`. -/
noncomputable def wState (t : ℂ) : QState :=
  ![![![0, t], ![t, 0]], ![![t, 0], ![0, 0]]]

private lemma normSq_ofReal_inv_sqrt {n : ℝ} (hn : 0 < n) :
    Complex.normSq (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = n⁻¹ := by
  rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hn.le]

private lemma norm_ofReal_inv_sqrt_pow4 {n : ℝ} (hn : 0 < n) :
    ‖(((Real.sqrt n)⁻¹ : ℝ) : ℂ)‖ ^ 4 = (n ^ 2)⁻¹ := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  rw [Complex.norm_real, abs_of_pos (by positivity)]
  rw [← Real.sq_sqrt hn.le]
  field_simp
  ring

theorem ghz_tangleABC (t : ℂ) : tangleABC (ghzState t) = 4 * (Complex.normSq t) ^ 2 := by
  simp [tangleABC, rhoA, ghzState, Matrix.det_fin_two, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem ghz_tangleAB (t : ℂ) : tangleAB (ghzState t) = 0 := by
  simp [tangleAB, frob, SAB, ghzState, Matrix.det_fin_two, Fin.sum_univ_two,
    Complex.normSq_eq_norm_sq]
  ring

theorem ghz_tangleAC (t : ℂ) : tangleAC (ghzState t) = 0 := by
  simp [tangleAC, frob, SAC, ghzState, Matrix.det_fin_two, Fin.sum_univ_two,
    Complex.normSq_eq_norm_sq]
  ring

theorem ghz_residualTangle (t : ℂ) : residualTangle (ghzState t) = 4 * ‖t‖ ^ 4 := by
  simp [residualTangle, SAB, SAC, ghzState, Matrix.det_fin_two]
  ring

theorem w_tangleABC (t : ℂ) : tangleABC (wState t) = 8 * (Complex.normSq t) ^ 2 := by
  simp [tangleABC, rhoA, wState, Matrix.det_fin_two, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem w_tangleAB (t : ℂ) : tangleAB (wState t) = 4 * ‖t‖ ^ 4 := by
  simp [tangleAB, frob, SAB, wState, Matrix.det_fin_two, Fin.sum_univ_two,
    Complex.normSq_eq_norm_sq]
  rw [show t * t + t * t = 2 * t ^ 2 by ring, norm_mul, norm_pow]
  norm_num
  ring

theorem w_tangleAC (t : ℂ) : tangleAC (wState t) = 4 * ‖t‖ ^ 4 := by
  simp [tangleAC, frob, SAC, wState, Matrix.det_fin_two, Fin.sum_univ_two,
    Complex.normSq_eq_norm_sq]
  rw [show t * t + t * t = 2 * t ^ 2 by ring, norm_mul, norm_pow]
  norm_num
  ring

theorem w_residualTangle (t : ℂ) : residualTangle (wState t) = 0 := by
  simp [residualTangle, SAB, SAC, wState, Matrix.det_fin_two]

/-- The normalised GHZ state. -/
noncomputable def ghzNormalized : QState := ghzState (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

/-- The normalised W state. -/
noncomputable def wNormalized : QState := wState (((Real.sqrt 3)⁻¹ : ℝ) : ℂ)

theorem ghzNormalized_isNormalized : IsNormalized ghzNormalized := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp [IsNormalized, ghzNormalized, ghzState, Fin.sum_univ_two, Complex.normSq_apply]
  field_simp
  nlinarith [h]

theorem wNormalized_isNormalized : IsNormalized wNormalized := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := by positivity
  simp [IsNormalized, wNormalized, wState, Fin.sum_univ_two, Complex.normSq_apply]
  field_simp
  nlinarith [h]

theorem ghzNormalized_tangleABC : tangleABC ghzNormalized = 1 := by
  rw [ghzNormalized, ghz_tangleABC, normSq_ofReal_inv_sqrt (by norm_num : (0:ℝ) < 2)]
  norm_num

theorem ghzNormalized_tangleAB : tangleAB ghzNormalized = 0 := ghz_tangleAB _

theorem ghzNormalized_tangleAC : tangleAC ghzNormalized = 0 := ghz_tangleAC _

theorem ghzNormalized_residualTangle : residualTangle ghzNormalized = 1 := by
  rw [ghzNormalized, ghz_residualTangle, norm_ofReal_inv_sqrt_pow4 (by norm_num : (0:ℝ) < 2)]
  norm_num

theorem wNormalized_tangleABC : tangleABC wNormalized = 8 / 9 := by
  rw [wNormalized, w_tangleABC, normSq_ofReal_inv_sqrt (by norm_num : (0:ℝ) < 3)]
  norm_num

theorem wNormalized_tangleAB : tangleAB wNormalized = 4 / 9 := by
  rw [wNormalized, w_tangleAB, norm_ofReal_inv_sqrt_pow4 (by norm_num : (0:ℝ) < 3)]
  norm_num

theorem wNormalized_tangleAC : tangleAC wNormalized = 4 / 9 := by
  rw [wNormalized, w_tangleAC, norm_ofReal_inv_sqrt_pow4 (by norm_num : (0:ℝ) < 3)]
  norm_num

theorem wNormalized_residualTangle : residualTangle wNormalized = 0 := w_residualTangle _

end QI

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

