/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring, so the header above is a plain
-- block comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Coffman–Kundu–Wootters monogamy inequality for three qubits

A pure state of three qubits `A`, `B`, `C` is described by its amplitude tensor
`ψ : Fin 2 → Fin 2 → Fin 2 → ℂ`, `ψ i j k` being the coefficient of `|i j k⟩`.

* The **tangle across the `A|BC` cut** is `τ_{A|BC} = 4 · det ρ_A`, where `ρ_A` is the
  reduced density matrix of qubit `A`.  (For a pure state this is the squared concurrence
  of the bipartite cut.)

* For the reduced two–qubit state `ρ_AB = Tr_C |ψ⟩⟨ψ|` Wootters' concurrence is computed
  from the *spin–flip* bilinear form.  Since `ρ_AB = Σ_k |v_k⟩⟨v_k|` with the (unnormalised)
  vectors `(v_k)_{ij} = ψ i j k` indexed by the traced-out qubit `C`, the square roots of the
  eigenvalues of `ρ_AB ρ̃_AB` are the singular values `s₁ ≥ s₂` of the complex symmetric `2 × 2`
  matrix
    `T_{kl} = Σ_{i i' j j'} (σ_y)_{i i'} (σ_y)_{j j'} ψ i j k * ψ i' j' l`,
  and Wootters' formula gives `C(ρ_AB) = s₁ - s₂` (the state has rank ≤ 2, so no truncation
  at `0` occurs).  Consequently
    `C(ρ_AB)² = s₁² + s₂² - 2 s₁ s₂ = ‖T‖_F² - 2 |det T|`,
  which is the closed formula used below as the definition of `concSqAB`; `concSqAC` is the
  same expression for the pair `A, C` (tracing out `B`).  The lemma
  `QI.concSq_eq_singular_value_diff_sq` re-derives the singular-value form `(s₁ - s₂)²`
  from this formula, and `QI.concSqAB_of_product` checks it against the pure-state
  concurrence on states of the form `|χ⟩_{AB} ⊗ |φ⟩_C`.

The main results are

* `QI.tangleA_eq_frob_add_frob` : `4 det ρ_A = ‖T^{AB}‖_F² + ‖T^{AC}‖_F²`;
* `QI.monogamy_ckw`            : `C(ρ_AB)² + C(ρ_AC)² ≤ τ_{A|BC}`  (the CKW inequality);
* `QI.ckw_exact`               : the sharpened identity
  `τ_{A|BC} = C(ρ_AB)² + C(ρ_AC)² + τ₃` with the residual three-tangle `τ₃ = 4 |det T^{AB}| ≥ 0`.

All quantities are homogeneous of degree `4` in `(ψ, ψ̄)`, so the results are stated (and proved)
without a normalisation assumption; the physically meaningful case `Σ |ψ i j k|² = 1` is
recorded separately in `QI.monogamy_ckw_normalized`.
-/

namespace QI

open Complex ComplexConjugate Finset

/-- Amplitude tensor of a pure three-qubit state. -/
abbrev State3 : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The Pauli matrix `σ_y`. -/
noncomputable def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Determinant of the reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|` of the first qubit. -/
noncomputable def detRhoA (ψ : State3) : ℝ :=
  (∑ j, ∑ k, normSq (ψ 0 j k)) * (∑ j, ∑ k, normSq (ψ 1 j k))
    - normSq (∑ j, ∑ k, ψ 0 j k * conj (ψ 1 j k))

/-- The tangle across the `A|BC` cut, `τ_{A|BC} = 4 det ρ_A`. -/
noncomputable def tangleA (ψ : State3) : ℝ := 4 * detRhoA ψ

/-- Spin-flip matrix of the reduced state `ρ_AB` (qubit `C`, index `k`, is traced out). -/
noncomputable def tAB (ψ : State3) (k l : Fin 2) : ℂ :=
  ∑ i, ∑ i', ∑ j, ∑ j', sigmaY i i' * sigmaY j j' * ψ i j k * ψ i' j' l

/-- Spin-flip matrix of the reduced state `ρ_AC` (qubit `B`, index `j`, is traced out). -/
noncomputable def tAC (ψ : State3) (j l : Fin 2) : ℂ :=
  ∑ i, ∑ i', ∑ k, ∑ k', sigmaY i i' * sigmaY k k' * ψ i j k * ψ i' l k'

/-- Squared Frobenius norm of a `2 × 2` complex matrix. -/
noncomputable def frob (T : Fin 2 → Fin 2 → ℂ) : ℝ := ∑ k, ∑ l, normSq (T k l)

/-- Determinant of a `2 × 2` complex matrix. -/
def det2 (T : Fin 2 → Fin 2 → ℂ) : ℂ := T 0 0 * T 1 1 - T 0 1 * T 1 0

/-- Wootters' squared concurrence of a rank-`≤ 2` two-qubit state with spin-flip matrix `T`. -/
noncomputable def concSqOf (T : Fin 2 → Fin 2 → ℂ) : ℝ := frob T - 2 * ‖det2 T‖

/-- Squared concurrence of the reduced state `ρ_AB`. -/
noncomputable def concSqAB (ψ : State3) : ℝ := concSqOf (tAB ψ)

/-- Squared concurrence of the reduced state `ρ_AC`. -/
noncomputable def concSqAC (ψ : State3) : ℝ := concSqOf (tAC ψ)

/-- The residual (three-)tangle. -/
noncomputable def tangle3 (ψ : State3) : ℝ := 4 * ‖det2 (tAB ψ)‖

/-! ### Explicit values of the spin-flip matrices -/

private lemma tAB_00 (ψ : State3) :
    tAB ψ 0 0 = -(2 * (ψ 0 0 0 * ψ 1 1 0 - ψ 0 1 0 * ψ 1 0 0)) := by
  simp only [tAB, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAB_11 (ψ : State3) :
    tAB ψ 1 1 = -(2 * (ψ 0 0 1 * ψ 1 1 1 - ψ 0 1 1 * ψ 1 0 1)) := by
  simp only [tAB, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAB_01 (ψ : State3) :
    tAB ψ 0 1 =
      -(ψ 0 0 0 * ψ 1 1 1 + ψ 0 0 1 * ψ 1 1 0 - ψ 0 1 0 * ψ 1 0 1 - ψ 0 1 1 * ψ 1 0 0) := by
  simp only [tAB, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAB_10 (ψ : State3) :
    tAB ψ 1 0 =
      -(ψ 0 0 0 * ψ 1 1 1 + ψ 0 0 1 * ψ 1 1 0 - ψ 0 1 0 * ψ 1 0 1 - ψ 0 1 1 * ψ 1 0 0) := by
  simp only [tAB, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAC_00 (ψ : State3) :
    tAC ψ 0 0 = -(2 * (ψ 0 0 0 * ψ 1 0 1 - ψ 0 0 1 * ψ 1 0 0)) := by
  simp only [tAC, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAC_11 (ψ : State3) :
    tAC ψ 1 1 = -(2 * (ψ 0 1 0 * ψ 1 1 1 - ψ 0 1 1 * ψ 1 1 0)) := by
  simp only [tAC, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAC_01 (ψ : State3) :
    tAC ψ 0 1 =
      -(ψ 0 0 0 * ψ 1 1 1 + ψ 0 1 0 * ψ 1 0 1 - ψ 0 0 1 * ψ 1 1 0 - ψ 0 1 1 * ψ 1 0 0) := by
  simp only [tAC, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma tAC_10 (ψ : State3) :
    tAC ψ 1 0 =
      -(ψ 0 0 0 * ψ 1 1 1 + ψ 0 1 0 * ψ 1 0 1 - ψ 0 0 1 * ψ 1 1 0 - ψ 0 1 1 * ψ 1 0 0) := by
  simp only [tAC, sigmaY, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma normSq_two_mul (z : ℂ) : normSq (2 * z) = 4 * normSq z := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-! ### The key algebraic identity -/

private lemma ckw_key (a b c d e f g h : ℂ) :
    4 * ((normSq a + normSq b + normSq c + normSq d) *
          (normSq e + normSq f + normSq g + normSq h)
        - normSq (a * conj e + b * conj f + c * conj g + d * conj h))
      = 4 * normSq (a * g - c * e) + 2 * normSq (a * h + b * g - c * f - d * e)
        + 4 * normSq (b * h - d * f)
        + 4 * normSq (a * f - b * e) + 2 * normSq (a * h + c * f - b * g - d * e)
        + 4 * normSq (c * h - d * g) := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

private lemma frob_tAB (ψ : State3) :
    frob (tAB ψ) = 4 * normSq (ψ 0 0 0 * ψ 1 1 0 - ψ 0 1 0 * ψ 1 0 0)
      + 2 * normSq (ψ 0 0 0 * ψ 1 1 1 + ψ 0 0 1 * ψ 1 1 0 - ψ 0 1 0 * ψ 1 0 1 - ψ 0 1 1 * ψ 1 0 0)
      + 4 * normSq (ψ 0 0 1 * ψ 1 1 1 - ψ 0 1 1 * ψ 1 0 1) := by
  simp only [frob, Fin.sum_univ_two, tAB_00, tAB_01, tAB_10, tAB_11, Complex.normSq_neg,
    normSq_two_mul]
  ring

private lemma frob_tAC (ψ : State3) :
    frob (tAC ψ) = 4 * normSq (ψ 0 0 0 * ψ 1 0 1 - ψ 0 0 1 * ψ 1 0 0)
      + 2 * normSq (ψ 0 0 0 * ψ 1 1 1 + ψ 0 1 0 * ψ 1 0 1 - ψ 0 0 1 * ψ 1 1 0 - ψ 0 1 1 * ψ 1 0 0)
      + 4 * normSq (ψ 0 1 0 * ψ 1 1 1 - ψ 0 1 1 * ψ 1 1 0) := by
  simp only [frob, Fin.sum_univ_two, tAC_00, tAC_01, tAC_10, tAC_11, Complex.normSq_neg,
    normSq_two_mul]
  ring

/-- **The tangle of the `A|BC` cut splits as the sum of the two spin-flip Frobenius norms.** -/
theorem tangleA_eq_frob_add_frob (ψ : State3) :
    tangleA ψ = frob (tAB ψ) + frob (tAC ψ) := by
  rw [frob_tAB, frob_tAC]
  simp only [tangleA, detRhoA, Fin.sum_univ_two]
  rw [show ψ 0 0 0 * conj (ψ 1 0 0) + ψ 0 0 1 * conj (ψ 1 0 1)
        + (ψ 0 1 0 * conj (ψ 1 1 0) + ψ 0 1 1 * conj (ψ 1 1 1))
      = ψ 0 0 0 * conj (ψ 1 0 0) + ψ 0 0 1 * conj (ψ 1 0 1) + ψ 0 1 0 * conj (ψ 1 1 0)
        + ψ 0 1 1 * conj (ψ 1 1 1) by ring]
  have := ckw_key (ψ 0 0 0) (ψ 0 0 1) (ψ 0 1 0) (ψ 0 1 1)
    (ψ 1 0 0) (ψ 1 0 1) (ψ 1 1 0) (ψ 1 1 1)
  linarith [this]

/-! ### Basic positivity facts -/

/-- For a complex symmetric `2 × 2` matrix, `‖T‖_F² ≥ 2 |det T|`; hence the squared
concurrence is nonnegative. -/
theorem concSqOf_nonneg (T : Fin 2 → Fin 2 → ℂ) (hsymm : T 0 1 = T 1 0) :
    0 ≤ concSqOf T := by
  have h1 : ‖det2 T‖ ≤ ‖T 0 0‖ * ‖T 1 1‖ + ‖T 0 1‖ * ‖T 1 0‖ := by
    calc ‖det2 T‖ ≤ ‖T 0 0 * T 1 1‖ + ‖T 0 1 * T 1 0‖ := norm_sub_le _ _
    _ = ‖T 0 0‖ * ‖T 1 1‖ + ‖T 0 1‖ * ‖T 1 0‖ := by rw [norm_mul, norm_mul]
  have h2 : 2 * (‖T 0 0‖ * ‖T 1 1‖) ≤ ‖T 0 0‖ ^ 2 + ‖T 1 1‖ ^ 2 := by
    nlinarith [sq_nonneg (‖T 0 0‖ - ‖T 1 1‖)]
  rw [hsymm] at h1
  simp only [concSqOf, frob, Fin.sum_univ_two, Complex.normSq_eq_norm_sq, hsymm]
  nlinarith [h1, h2, norm_nonneg (T 1 0)]

theorem concSqAB_nonneg (ψ : State3) : 0 ≤ concSqAB ψ :=
  concSqOf_nonneg _ (by rw [tAB_01, tAB_10])

theorem concSqAC_nonneg (ψ : State3) : 0 ≤ concSqAC ψ :=
  concSqOf_nonneg _ (by rw [tAC_01, tAC_10])

/-- The two spin-flip determinants agree; their common value is (up to a factor) Cayley's
hyperdeterminant of the amplitude tensor. -/
theorem det2_tAB_eq_det2_tAC (ψ : State3) : det2 (tAB ψ) = det2 (tAC ψ) := by
  simp only [det2, tAB_00, tAB_01, tAB_10, tAB_11, tAC_00, tAC_01, tAC_10, tAC_11]
  ring

/-! ### The CKW inequality -/

/-- **Coffman–Kundu–Wootters monogamy inequality** for a pure state of three qubits:
the entanglement of qubit `A` with `B` plus its entanglement with `C`, measured by the squared
concurrences of the reduced two-qubit states, never exceeds the tangle of `A` with the pair
`BC`. -/
theorem monogamy_ckw (ψ : State3) : concSqAB ψ + concSqAC ψ ≤ tangleA ψ := by
  have h := tangleA_eq_frob_add_frob ψ
  simp only [concSqAB, concSqAC, concSqOf]
  have h1 : (0:ℝ) ≤ ‖det2 (tAB ψ)‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖det2 (tAC ψ)‖ := norm_nonneg _
  linarith

/-- The CKW inequality, stated for a normalised state (the normalisation hypothesis is not
needed for the proof, since every quantity involved is homogeneous of degree `4`). -/
theorem monogamy_ckw_normalized (ψ : State3)
    (_hnorm : ∑ i, ∑ j, ∑ k, normSq (ψ i j k) = 1) :
    concSqAB ψ + concSqAC ψ ≤ tangleA ψ :=
  monogamy_ckw ψ

/-- The sharp form of the CKW inequality: the deficit is the residual three-tangle. -/
theorem ckw_exact (ψ : State3) :
    tangleA ψ = concSqAB ψ + concSqAC ψ + tangle3 ψ := by
  have h := tangleA_eq_frob_add_frob ψ
  have hd := det2_tAB_eq_det2_tAC ψ
  simp only [concSqAB, concSqAC, concSqOf, tangle3, hd]
  linarith

theorem tangle3_nonneg (ψ : State3) : 0 ≤ tangle3 ψ := by
  have : (0:ℝ) ≤ ‖det2 (tAB ψ)‖ := norm_nonneg _
  simp only [tangle3]
  linarith

/-! ### Sanity checks -/

/-- The squared concurrence, as defined here, is the square of the difference of the two
singular values of the spin-flip matrix. -/
theorem concSq_eq_singular_value_diff_sq (T : Fin 2 → Fin 2 → ℂ) (hsymm : T 0 1 = T 1 0) :
    ∃ s₁ s₂ : ℝ, 0 ≤ s₂ ∧ s₂ ≤ s₁ ∧ s₁ ^ 2 + s₂ ^ 2 = frob T ∧ s₁ * s₂ = ‖det2 T‖ ∧
      concSqOf T = (s₁ - s₂) ^ 2 := by
  set d : ℝ := ‖det2 T‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hB : 0 ≤ frob T - 2 * d := concSqOf_nonneg T hsymm
  have hA : 0 ≤ frob T + 2 * d := by linarith
  set A := Real.sqrt (frob T + 2 * d) with hAdef
  set B := Real.sqrt (frob T - 2 * d) with hBdef
  have hA2 : A ^ 2 = frob T + 2 * d := Real.sq_sqrt hA
  have hB2 : B ^ 2 = frob T - 2 * d := Real.sq_sqrt hB
  have hAnn : 0 ≤ A := Real.sqrt_nonneg _
  have hBnn : 0 ≤ B := Real.sqrt_nonneg _
  have hBA : B ≤ A := Real.sqrt_le_sqrt (by linarith)
  refine ⟨(A + B) / 2, (A - B) / 2, by linarith, by linarith, by nlinarith, by nlinarith, ?_⟩
  have : ((A + B) / 2 - (A - B) / 2) ^ 2 = B ^ 2 := by ring_nf
  rw [this, hB2, concSqOf]

/-- On a state of the form `|χ⟩_{AB} ⊗ |φ⟩_C` the formula for `C(ρ_AB)²` reduces to the
squared pure-state concurrence `4 |χ₀₀ χ₁₁ - χ₀₁ χ₁₀|²` of `|χ⟩` (for a normalised `|φ⟩`). -/
theorem concSqAB_of_product (χ : Fin 2 → Fin 2 → ℂ) (φ : Fin 2 → ℂ)
    (hφ : normSq (φ 0) + normSq (φ 1) = 1) :
    concSqAB (fun i j k => χ i j * φ k)
      = 4 * normSq (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) := by
  have hdet : det2 (tAB fun i j k => χ i j * φ k) = 0 := by
    simp only [det2, tAB_00, tAB_01, tAB_10, tAB_11]
    ring
  simp only [concSqAB, concSqOf, hdet, norm_zero, mul_zero, sub_zero, frob_tAB]
  have h1 : normSq (χ 0 0 * φ 0 * (χ 1 1 * φ 0) - χ 0 1 * φ 0 * (χ 1 0 * φ 0))
      = normSq (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * normSq (φ 0) ^ 2 := by
    rw [show χ 0 0 * φ 0 * (χ 1 1 * φ 0) - χ 0 1 * φ 0 * (χ 1 0 * φ 0)
        = (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * (φ 0 * φ 0) by ring]
    rw [map_mul, map_mul]; ring
  have h2 : normSq (χ 0 0 * φ 1 * (χ 1 1 * φ 1) - χ 0 1 * φ 1 * (χ 1 0 * φ 1))
      = normSq (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * normSq (φ 1) ^ 2 := by
    rw [show χ 0 0 * φ 1 * (χ 1 1 * φ 1) - χ 0 1 * φ 1 * (χ 1 0 * φ 1)
        = (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * (φ 1 * φ 1) by ring]
    rw [map_mul, map_mul]; ring
  have h3 : normSq (χ 0 0 * φ 0 * (χ 1 1 * φ 1) + χ 0 0 * φ 1 * (χ 1 1 * φ 0)
        - χ 0 1 * φ 0 * (χ 1 0 * φ 1) - χ 0 1 * φ 1 * (χ 1 0 * φ 0))
      = 4 * normSq (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * (normSq (φ 0) * normSq (φ 1)) := by
    rw [show χ 0 0 * φ 0 * (χ 1 1 * φ 1) + χ 0 0 * φ 1 * (χ 1 1 * φ 0)
        - χ 0 1 * φ 0 * (χ 1 0 * φ 1) - χ 0 1 * φ 1 * (χ 1 0 * φ 0)
        = (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * (2 * (φ 0 * φ 1)) by ring]
    rw [map_mul, normSq_two_mul, map_mul]
    ring
  rw [h1, h2, h3]
  linear_combination (4 * normSq (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) *
    (normSq (φ 0) + normSq (φ 1) + 1)) * hφ

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`: no pairwise concurrence, all the
entanglement is genuinely tripartite. -/
noncomputable def ghz : State3 := ![![![1, 0], ![0, 0]], ![![0, 0], ![0, 1]]]

theorem ghz_no_pairwise_concurrence :
    concSqAB ghz = 0 ∧ concSqAC ghz = 0 ∧ tangleA ghz = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [concSqAB, concSqOf, frob_tAB, det2, tAB_00, tAB_01, tAB_10, tAB_11, ghz]
    norm_num [Complex.normSq_apply]
  · simp only [concSqAC, concSqOf, frob_tAC, det2, tAC_00, tAC_01, tAC_10, tAC_11, ghz]
    norm_num [Complex.normSq_apply]
  · simp only [tangleA, detRhoA, Fin.sum_univ_two, ghz]
    norm_num [Complex.normSq_apply]

/-- The (unnormalised) W state `|001⟩ + |010⟩ + |100⟩` saturates the CKW inequality. -/
noncomputable def wState : State3 := ![![![0, 1], ![1, 0]], ![![1, 0], ![0, 0]]]

theorem wState_saturates_ckw : concSqAB wState + concSqAC wState = tangleA wState := by
  have hAB : concSqAB wState = 4 := by
    simp only [concSqAB, concSqOf, frob_tAB, det2, tAB_00, tAB_01, tAB_10, tAB_11, wState]
    norm_num [Complex.normSq_apply]
  have hAC : concSqAC wState = 4 := by
    simp only [concSqAC, concSqOf, frob_tAC, det2, tAC_00, tAC_01, tAC_10, tAC_11, wState]
    norm_num [Complex.normSq_apply]
  have hT : tangleA wState = 8 := by
    simp only [tangleA, detRhoA, Fin.sum_univ_two, wState]
    norm_num [Complex.normSq_apply]
  rw [hAB, hAC, hT]; norm_num

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

