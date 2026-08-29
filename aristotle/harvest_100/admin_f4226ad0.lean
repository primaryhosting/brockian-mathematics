/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment and is reproduced verbatim as the module docstring below.)

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

open ComplexConjugate

/-! ## Setup

A pure state of three qubits `A`, `B`, `C` is given by its amplitudes
`psi i j k` in the computational basis `|ijk⟩`, `i j k : Fin 2`.
All quantities below are homogeneous of degree `(2,2)` in `(psi, conj psi)`, so
they are the usual physical quantities as soon as `psi` is normalized; no
normalization hypothesis is needed for the statements.
-/

/-- The reduced density matrix of qubit `A`,
`(ρ_A)_{i i'} = ∑_{j k} ψ_{ijk} conj ψ_{i'jk}`. -/
noncomputable def rhoA (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j : Fin 2, ∑ k : Fin 2, psi i j k * conj (psi i' j k)

/-- The tangle across the bipartition `A|BC` of a three-qubit pure state,
`τ_{A(BC)} = C²_{A(BC)} = 4 det ρ_A`. -/
noncomputable def tangleABC (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : ℝ :=
  4 * ((rhoA psi).det).re

/-- The `2 × 2` concurrence matrix of the pair `A B`.

Writing the state as `|ψ⟩ = ∑_k |φ_k⟩_{AB} ⊗ |k⟩_C`, this is the symmetric matrix
`T_{kl} = ⟨φ_k^*| σ_y ⊗ σ_y |φ_l⟩ = φ_k^T (σ_y ⊗ σ_y) φ_l`, whose singular values
`d₁ ≥ d₂` are the (at most two) nonzero square-root eigenvalues of `ρ_{AB} ρ̃_{AB}`
occurring in Wootters' formula. -/
noncomputable def concMatAB (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun k l =>
    -(psi 0 0 k * psi 1 1 l) + psi 0 1 k * psi 1 0 l + psi 1 0 k * psi 0 1 l
      - psi 1 1 k * psi 0 0 l

/-- The `2 × 2` concurrence matrix of the pair `A C` (the spectator is now `B`). -/
noncomputable def concMatAC (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j l =>
    -(psi 0 j 0 * psi 1 l 1) + psi 0 j 1 * psi 1 l 0 + psi 1 j 0 * psi 0 l 1
      - psi 1 j 1 * psi 0 l 0

/-- The squared Wootters concurrence attached to a `2 × 2` concurrence matrix `T`:
if `d₁ ≥ d₂ ≥ 0` are the singular values of `T`, then the concurrence of the
corresponding (rank ≤ 2) two-qubit mixed state is `C = d₁ - d₂`, so
`C² = d₁² + d₂² - 2 d₁ d₂ = ‖T‖_F² - 2 |det T|`. -/
noncomputable def sqConcurrence (T : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (∑ k : Fin 2, ∑ l : Fin 2, ‖T k l‖ ^ 2) - 2 * ‖T.det‖

/-- Cayley's hyperdeterminant of a `2 × 2 × 2` array of amplitudes. -/
noncomputable def hyperdet (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : ℂ :=
  psi 0 0 0 ^ 2 * psi 1 1 1 ^ 2 + psi 0 0 1 ^ 2 * psi 1 1 0 ^ 2
    + psi 0 1 0 ^ 2 * psi 1 0 1 ^ 2 + psi 1 0 0 ^ 2 * psi 0 1 1 ^ 2
    - 2 * (psi 0 0 0 * psi 1 1 1 * psi 0 0 1 * psi 1 1 0
        + psi 0 0 0 * psi 1 1 1 * psi 0 1 0 * psi 1 0 1
        + psi 0 0 0 * psi 1 1 1 * psi 1 0 0 * psi 0 1 1
        + psi 0 0 1 * psi 1 1 0 * psi 0 1 0 * psi 1 0 1
        + psi 0 0 1 * psi 1 1 0 * psi 1 0 0 * psi 0 1 1
        + psi 0 1 0 * psi 1 0 1 * psi 1 0 0 * psi 0 1 1)
    + 4 * (psi 0 0 0 * psi 0 1 1 * psi 1 0 1 * psi 1 1 0
        + psi 1 1 1 * psi 1 0 0 * psi 0 1 0 * psi 0 0 1)

/-- The residual (three-way) tangle. -/
noncomputable def tangle3 (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : ℝ :=
  4 * ‖hyperdet psi‖

/-! ## Key algebraic identities -/

/-- The core identity, in complex form: `4 det ρ_A = ‖T_{AB}‖_F² + ‖T_{AC}‖_F²`. -/
theorem four_det_rhoA_complex (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    (4 : ℂ) * (rhoA psi).det
      = (∑ k : Fin 2, ∑ l : Fin 2, concMatAB psi k l * conj (concMatAB psi k l))
        + (∑ k : Fin 2, ∑ l : Fin 2, concMatAC psi k l * conj (concMatAC psi k l)) := by
  simp only [rhoA, concMatAB, concMatAC, Matrix.det_fin_two, Matrix.of_apply, Fin.sum_univ_two,
    map_add, map_sub, map_neg, map_mul]
  ring

/-- The tangle across `A|BC` is the sum of the squared Frobenius norms of the two
concurrence matrices. -/
theorem tangleABC_eq_frobenius (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    tangleABC psi
      = (∑ k : Fin 2, ∑ l : Fin 2, ‖concMatAB psi k l‖ ^ 2)
        + (∑ k : Fin 2, ∑ l : Fin 2, ‖concMatAC psi k l‖ ^ 2) := by
  have h := congrArg Complex.re (four_det_rhoA_complex psi)
  simpa [tangleABC, Complex.mul_conj, Complex.normSq_eq_abs, Fin.sum_univ_two,
    Complex.sq_abs] using h

/-- The determinant of the `AB` concurrence matrix is (minus) the hyperdeterminant. -/
theorem det_concMatAB (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    (concMatAB psi).det = -hyperdet psi := by
  simp only [concMatAB, hyperdet, Matrix.det_fin_two, Matrix.of_apply]
  ring

/-- The determinant of the `AC` concurrence matrix is (minus) the hyperdeterminant. -/
theorem det_concMatAC (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    (concMatAC psi).det = -hyperdet psi := by
  simp only [concMatAC, hyperdet, Matrix.det_fin_two, Matrix.of_apply]
  ring

/-- A squared concurrence is nonnegative: `‖T‖_F² ≥ 2 |det T|`. -/
theorem sqConcurrence_nonneg (T : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ sqConcurrence T := by
  have hdet : ‖T.det‖ ≤ ‖T 0 0‖ * ‖T 1 1‖ + ‖T 0 1‖ * ‖T 1 0‖ := by
    rw [Matrix.det_fin_two]
    calc ‖T 0 0 * T 1 1 - T 0 1 * T 1 0‖ ≤ ‖T 0 0 * T 1 1‖ + ‖T 0 1 * T 1 0‖ :=
          norm_sub_le _ _
      _ = ‖T 0 0‖ * ‖T 1 1‖ + ‖T 0 1‖ * ‖T 1 0‖ := by rw [norm_mul, norm_mul]
  have h1 : (0:ℝ) ≤ (‖T 0 0‖ - ‖T 1 1‖) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (‖T 0 1‖ - ‖T 1 0‖) ^ 2 := sq_nonneg _
  simp only [sqConcurrence, Fin.sum_univ_two]
  nlinarith [hdet, h1, h2]

/-! ## The CKW monogamy inequality -/

/-- **The CKW identity**: for any three-qubit pure state, the tangle across the
`A|BC` cut is the sum of the two pairwise squared concurrences plus the residual
three-tangle `4 |Hdet ψ|`. -/
theorem ckw_identity (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    tangleABC psi
      = sqConcurrence (concMatAB psi) + sqConcurrence (concMatAC psi) + tangle3 psi := by
  simp only [sqConcurrence, tangle3, det_concMatAB, det_concMatAC, norm_neg,
    tangleABC_eq_frobenius]
  ring

/-- **Monogamy of entanglement (Coffman–Kundu–Wootters)**: for every pure state of
three qubits, the squared concurrences of the two reduced pairs `AB` and `AC` sum to
at most the squared concurrence (tangle) of `A` with the pair `BC`:
`C²_{AB} + C²_{AC} ≤ C²_{A(BC)} = 4 det ρ_A`. -/
theorem monogamy_ckw (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    sqConcurrence (concMatAB psi) + sqConcurrence (concMatAC psi) ≤ tangleABC psi := by
  have h : 0 ≤ tangle3 psi := by
    simp only [tangle3]
    positivity
  have := ckw_identity psi
  linarith

end QI

