/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## Monogamy of entanglement: the Coffman–Kundu–Wootters inequality

For a pure state `|ψ⟩` of three qubits `A`, `B`, `C` with amplitudes
`a i j k = ⟨ijk|ψ⟩`, the CKW inequality states

`C²(A,B) + C²(A,C) ≤ τ(A|BC)`,

where `C(A,B)`, `C(A,C)` are Wootters' concurrences of the two–qubit reduced
states `ρ_AB`, `ρ_AC`, and `τ(A|BC) = C²(A|BC) = 4 det ρ_A` is the tangle of
qubit `A` against the pair `BC`.

### How the quantities are expressed here

*The tangle* `τ(A|BC)` is `4 · det ρ_A`, with `ρ_A` the reduced density matrix
of qubit `A` (`QI.rhoA`, `QI.tangleA`).

*The two–qubit concurrences.*  Tracing out qubit `C` decomposes the reduced
state as `ρ_AB = Σ_k |w_k⟩⟨w_k|` with the (unnormalised) vectors
`(w_k)_{ij} = a i j k`.  Wootters' theory expresses the concurrence of a state
given by such a decomposition through the symmetric matrix
`T_{kl} = w_kᵀ (σ_y ⊗ σ_y) w_l`: the square roots `λ₁ ≥ λ₂ ≥ …` of the
eigenvalues of `ρ ρ̃` are exactly the singular values `s₁ ≥ s₂` of `T`
(all further ones vanish, `ρ_AB` having rank at most two), so

`C(A,B) = max (0, λ₁ - λ₂ - λ₃ - λ₄) = s₁ - s₂`, hence
`C²(A,B) = s₁² + s₂² - 2 s₁ s₂ = ‖T‖_F² - 2 |det T|`.

Accordingly `QI.concSq` computes `‖T‖_F² - 2|det T|` and the two concurrences
squared are `QI.concSqAB` and `QI.concSqAC`, built from the matrices `QI.TAB`
and `QI.TAC`.  The bridge back to the density matrix is recorded in
`QI.trace_rhoAB_spinFlip` (`tr (ρ_AB ρ̃_AB) = ‖T‖_F² = λ₁² + λ₂²`) and
`QI.trace_rhoAC_spinFlip`.

### The proof

Everything follows from one polynomial identity in the amplitudes
(`QI.frobenius_add_frobenius_eq_tangle`):

`‖T_AB‖_F² + ‖T_AC‖_F² = 4 det ρ_A`,

together with `det T_AB = det T_AC` (`QI.det_TAB_eq_det_TAC`), whose modulus is
a quarter of the residual three–tangle.  This yields the CKW *equality*
`C²(A,B) + C²(A,C) + τ₃ = τ(A|BC)` (`QI.ckw_equality`) and hence the
inequality, since `τ₃ ≥ 0`.

No normalisation of the amplitudes is needed: every quantity involved is
homogeneous of bidegree `(2,2)` in `(a, ā)`, so the statements hold verbatim
for normalised states.
-/

namespace QI

open Complex Matrix

/-- Amplitudes `a i j k = ⟨ijk|ψ⟩` of a three–qubit state. -/
abbrev Amp : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`. -/
noncomputable def rhoA (a : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j, ∑ k, a i j k * (starRingEnd ℂ) (a i' j k)

/-- The tangle of qubit `A` against the pair `BC`, `τ(A|BC) = 4 det ρ_A`. -/
noncomputable def tangleA (a : Amp) : ℝ := 4 * (rhoA a).det.re

/-- Wootters' `T`-matrix for the pair `AB`: `T k l = w_kᵀ (σ_y ⊗ σ_y) w_l`,
where `(w_k)_{ij} = a i j k` are the vectors of the rank-≤2 decomposition of
`ρ_AB` obtained by tracing out qubit `C`. -/
noncomputable def TAB (a : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun k l =>
    -(a 0 0 k * a 1 1 l) + a 0 1 k * a 1 0 l + a 1 0 k * a 0 1 l - a 1 1 k * a 0 0 l

/-- Wootters' `T`-matrix for the pair `AC`. -/
noncomputable def TAC (a : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j l =>
    -(a 0 j 0 * a 1 l 1) + a 0 j 1 * a 1 l 0 + a 1 j 0 * a 0 l 1 - a 1 j 1 * a 0 l 0

/-- Squared Frobenius norm of a `2 × 2` complex matrix. -/
noncomputable def frob (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ k, ∑ l, normSq (M k l)

/-- The squared concurrence attached to a Wootters `T`-matrix of a rank-≤2
two–qubit state: `(s₁ - s₂)² = ‖T‖_F² - 2|det T|`, with `s₁ ≥ s₂` the singular
values of `T`. -/
noncomputable def concSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := frob M - 2 * ‖M.det‖

/-- Squared concurrence `C²(A,B)` of the reduced state `ρ_AB`. -/
noncomputable def concSqAB (a : Amp) : ℝ := concSq (TAB a)

/-- Squared concurrence `C²(A,C)` of the reduced state `ρ_AC`. -/
noncomputable def concSqAC (a : Amp) : ℝ := concSq (TAC a)

/-- The residual three–tangle `τ₃ = 4 |det T|` (four times the modulus of
Cayley's hyperdeterminant of the amplitude array). -/
noncomputable def tau3 (a : Amp) : ℝ := 4 * ‖(TAB a).det‖

/-! ### Bridge to the reduced density matrices

The `T`-matrices above are tied to Wootters' spin-flip construction by
`tr (ρ ρ̃) = ‖T‖_F² = λ₁² + λ₂²`, proved below for both `ρ_AB` and `ρ_AC`. -/

/-- The Pauli matrix `σ_y`. -/
noncomputable def sy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The two-qubit spin-flip operator `σ_y ⊗ σ_y`. -/
noncomputable def Ymat : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => sy p.1 q.1 * sy p.2 q.2

/-- Wootters' spin flip `ρ ↦ ρ̃ = (σ_y ⊗ σ_y) ρ̄ (σ_y ⊗ σ_y)`. -/
noncomputable def spinFlip (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Ymat * M.map (starRingEnd ℂ) * Ymat

/-- The reduced density matrix `ρ_AB` (qubit `C` traced out). -/
noncomputable def rhoAB (a : Amp) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => ∑ k, a p.1 p.2 k * (starRingEnd ℂ) (a q.1 q.2 k)

/-- The reduced density matrix `ρ_AC` (qubit `B` traced out). -/
noncomputable def rhoAC (a : Amp) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => ∑ j, a p.1 j p.2 * (starRingEnd ℂ) (a q.1 j q.2)

/-- `tr (ρ_AB ρ̃_AB) = ‖T_AB‖_F²`, i.e. the sum of the eigenvalues of `ρ ρ̃`
equals the sum of the squared singular values of the Wootters matrix. -/
theorem trace_rhoAB_spinFlip (a : Amp) :
    (rhoAB a * spinFlip (rhoAB a)).trace = ((frob (TAB a) : ℝ) : ℂ) := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, spinFlip, rhoAB, Ymat, sy, TAB,
    Matrix.of_apply, Matrix.map_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> ring

/-- `tr (ρ_AC ρ̃_AC) = ‖T_AC‖_F²`. -/
theorem trace_rhoAC_spinFlip (a : Amp) :
    (rhoAC a * spinFlip (rhoAC a)).trace = ((frob (TAC a) : ℝ) : ℂ) := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, spinFlip, rhoAC, Ymat, sy, TAC,
    Matrix.of_apply, Matrix.map_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> ring

/-! ### Explicit real forms -/

lemma tangleA_eq (a : Amp) :
    tangleA a =
      4 * (((∑ j, ∑ k, normSq (a 0 j k)) * (∑ j, ∑ k, normSq (a 1 j k)))
        - normSq (∑ j, ∑ k, a 0 j k * (starRingEnd ℂ) (a 1 j k))) := by
  simp [tangleA, rhoA, Matrix.det_fin_two, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re]
  ring

/-! ### The key polynomial identity -/

/-- The two Wootters matrices carry, in total, exactly the tangle of `A`
against `BC`. -/
theorem frobenius_add_frobenius_eq_tangle (a : Amp) :
    frob (TAB a) + frob (TAC a) = tangleA a := by
  rw [tangleA_eq]
  simp only [frob, TAB, TAC, Matrix.of_apply]
  simp [Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im]
  ring

/-- The two Wootters matrices have the same determinant; its modulus is a
quarter of the three–tangle (this is the permutation invariance of the residual
tangle). -/
theorem det_TAB_eq_det_TAC (a : Amp) : (TAB a).det = (TAC a).det := by
  simp only [Matrix.det_fin_two, TAB, TAC, Matrix.of_apply]
  ring

/-! ### Nonnegativity -/

lemma two_norm_det_le_frob (M : Matrix (Fin 2) (Fin 2) ℂ) : 2 * ‖M.det‖ ≤ frob M := by
  have hdet : ‖M.det‖ ≤ ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by
    rw [Matrix.det_fin_two]
    calc ‖M 0 0 * M 1 1 - M 0 1 * M 1 0‖
        ≤ ‖M 0 0 * M 1 1‖ + ‖M 0 1 * M 1 0‖ := norm_sub_le _ _
      _ = ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by rw [norm_mul, norm_mul]
  have h1 : 2 * (‖M 0 0‖ * ‖M 1 1‖) ≤ ‖M 0 0‖ ^ 2 + ‖M 1 1‖ ^ 2 := by nlinarith [sq_nonneg (‖M 0 0‖ - ‖M 1 1‖)]
  have h2 : 2 * (‖M 0 1‖ * ‖M 1 0‖) ≤ ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 := by nlinarith [sq_nonneg (‖M 0 1‖ - ‖M 1 0‖)]
  have hn : ∀ z : ℂ, normSq z = ‖z‖ ^ 2 := fun z => Complex.normSq_eq_norm_sq z
  simp only [frob, Fin.sum_univ_two, hn]
  linarith

lemma concSq_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ concSq M := by
  have := two_norm_det_le_frob M
  simp only [concSq]
  linarith

lemma tau3_nonneg (a : Amp) : 0 ≤ tau3 a := by
  simp only [tau3]
  positivity

/-! ### The CKW equality and the monogamy inequality -/

/-- **CKW equality.**  For a pure three–qubit state, the tangle of `A` against
`BC` splits into the two pairwise squared concurrences plus the residual
three–tangle. -/
theorem ckw_equality (a : Amp) :
    concSqAB a + concSqAC a + tau3 a = tangleA a := by
  have h := frobenius_add_frobenius_eq_tangle a
  simp only [concSqAB, concSqAC, concSq, tau3, det_TAB_eq_det_TAC a]
  linarith

/-- **Monogamy of entanglement (Coffman–Kundu–Wootters).**  For any pure state
of three qubits, the squared concurrences of qubit `A` with `B` and with `C`
cannot together exceed the tangle of `A` with the pair `BC`. -/
theorem monogamy_ckw (a : Amp) :
    concSqAB a + concSqAC a ≤ tangleA a := by
  have h := ckw_equality a
  have := tau3_nonneg a
  linarith

/-! ### Sanity checks on the standard examples

The GHZ state has no two–party entanglement but maximal three–tangle, while the
W state has no three–tangle and shares its entanglement pairwise. -/

/-- The GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz : Amp := fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- The W state `(|001⟩ + |010⟩ + |100⟩)/√3`. -/
noncomputable def wst : Amp :=
  fun i j k => if (i : ℕ) + (j : ℕ) + (k : ℕ) = 1 then ((Real.sqrt 3)⁻¹ : ℝ) else 0

private lemma sqrt_facts (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt n ^ 2 = n ∧ Real.sqrt n ^ 4 = n ^ 2 ∧ Real.sqrt n ^ 8 = n ^ 4 := by
  have h2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn
  refine ⟨h2, ?_, ?_⟩
  · have h : Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 := by ring
    rw [h, h2]
  · have h : Real.sqrt n ^ 8 = (Real.sqrt n ^ 2) ^ 4 := by ring
    rw [h, h2]

lemma ghz_tangleA : tangleA ghz = 1 := by
  obtain ⟨h2, h4, h8⟩ := sqrt_facts 2 (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [tangleA_eq, ghz, Fin.sum_univ_two]
  norm_num [Complex.normSq_apply, Complex.ext_iff]
  try field_simp
  try nlinarith [h2, h4, h8]

lemma ghz_concSqAB : concSqAB ghz = 0 := by
  obtain ⟨h2, h4, h8⟩ := sqrt_facts 2 (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have habs : |Real.sqrt 2| = Real.sqrt 2 := abs_of_nonneg (Real.sqrt_nonneg 2)
  simp only [concSqAB, concSq, frob, TAB, ghz, Matrix.det_fin_two, Matrix.of_apply,
    Fin.sum_univ_two]
  norm_num [Complex.normSq_apply, Complex.ext_iff, habs]
  try field_simp
  try nlinarith [h2, h4, h8]

lemma ghz_concSqAC : concSqAC ghz = 0 := by
  obtain ⟨h2, h4, h8⟩ := sqrt_facts 2 (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have habs : |Real.sqrt 2| = Real.sqrt 2 := abs_of_nonneg (Real.sqrt_nonneg 2)
  simp only [concSqAC, concSq, frob, TAC, ghz, Matrix.det_fin_two, Matrix.of_apply,
    Fin.sum_univ_two]
  norm_num [Complex.normSq_apply, Complex.ext_iff, habs]
  try field_simp
  try nlinarith [h2, h4, h8]

lemma ghz_tau3 : tau3 ghz = 1 := by
  have h := ckw_equality ghz
  rw [ghz_concSqAB, ghz_concSqAC, ghz_tangleA] at h
  linarith

lemma w_tangleA : tangleA wst = 8/9 := by
  obtain ⟨h2, h4, h8⟩ := sqrt_facts 3 (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  simp only [tangleA_eq, wst, Fin.sum_univ_two]
  norm_num [Complex.normSq_apply, Complex.ext_iff]
  try field_simp
  try nlinarith [h2, h4, h8]

lemma w_concSqAB : concSqAB wst = 4/9 := by
  obtain ⟨h2, h4, h8⟩ := sqrt_facts 3 (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have habs : |Real.sqrt 3| = Real.sqrt 3 := abs_of_nonneg (Real.sqrt_nonneg 3)
  simp only [concSqAB, concSq, frob, TAB, wst, Matrix.det_fin_two, Matrix.of_apply,
    Fin.sum_univ_two]
  norm_num [Complex.normSq_apply, Complex.ext_iff, habs]
  try field_simp
  try nlinarith [h2, h4, h8]

lemma w_concSqAC : concSqAC wst = 4/9 := by
  obtain ⟨h2, h4, h8⟩ := sqrt_facts 3 (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have habs : |Real.sqrt 3| = Real.sqrt 3 := abs_of_nonneg (Real.sqrt_nonneg 3)
  simp only [concSqAC, concSq, frob, TAC, wst, Matrix.det_fin_two, Matrix.of_apply,
    Fin.sum_univ_two]
  norm_num [Complex.normSq_apply, Complex.ext_iff, habs]
  try field_simp
  try nlinarith [h2, h4, h8]

lemma w_tau3 : tau3 wst = 0 := by
  have h := ckw_equality wst
  rw [w_concSqAB, w_concSqAC, w_tangleA] at h
  linarith

end QI

