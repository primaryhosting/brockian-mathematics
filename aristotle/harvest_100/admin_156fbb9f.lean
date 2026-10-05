/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment on the first lines of the file, because
Lean 4 does not permit a module docstring to precede the `import` commands.)

## Contents

* `QPhys.heisenberg_uncertainty`: for a normalized state `ψ` of a complex inner product
  space and symmetric operators `X`, `P` satisfying the canonical commutation relation
  `[X, P] ψ = i ℏ ψ`, the standard deviations satisfy `Δx · Δp ≥ ℏ / 2`.
  The proof is the classical one: the commutator identity computes
  `⟪u, v⟫ - ⟪v, u⟫ = i ℏ` for the centred vectors `u = (X - ⟨X⟩)ψ`, `v = (P - ⟨P⟩)ψ`,
  and Cauchy–Schwarz bounds each inner product by `‖u‖ ‖v‖ = Δx · Δp`.
* `QPhys.heisenberg_uncertainty_sharp`: the hypotheses are satisfiable and the bound is
  attained, for every `ℏ ≥ 0`.
-/

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expectation values of a symmetric operator in a state are real. -/
lemma expectation_real (X : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, inner ℂ (X u) v = inner ℂ u (X v)) (psi : E) :
    (starRingEnd ℂ) (inner ℂ psi (X psi)) = inner ℂ psi (X psi) := by
  rw [inner_conj_symm, hX]

/-- The commutator identity: for symmetric `X`, `P` with `[X, P] ψ = i ℏ ψ` and `‖ψ‖ = 1`,
the difference of the two inner products of the centred vectors equals `i ℏ`. -/
lemma inner_comm_diff (X P : E →ₗ[ℂ] E) (hbar : ℝ) (psi : E) (hpsi : ‖psi‖ = 1)
    (hX : ∀ u v : E, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : E, inner ℂ (P u) v = inner ℂ u (P v))
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    inner ℂ (X psi - (inner ℂ psi (X psi) : ℂ) • psi)
        (P psi - (inner ℂ psi (P psi) : ℂ) • psi)
      - inner ℂ (P psi - (inner ℂ psi (P psi) : ℂ) • psi)
        (X psi - (inner ℂ psi (X psi) : ℂ) • psi)
      = Complex.I * (hbar : ℂ) := by
  have hnorm : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  set a : ℂ := inner ℂ psi (X psi) with ha
  set b : ℂ := inner ℂ psi (P psi) with hb
  have hac : (starRingEnd ℂ) a = a := expectation_real X hX psi
  have hbc : (starRingEnd ℂ) b = b := expectation_real P hP psi
  have hXpsi : (inner ℂ (X psi) psi : ℂ) = a := by rw [ha, hX]
  have hPpsi : (inner ℂ (P psi) psi : ℂ) = b := by rw [hb, hP]
  have key : (inner ℂ (X psi) (P psi) : ℂ) - inner ℂ (P psi) (X psi)
      = Complex.I * (hbar : ℂ) := by
    have h1 : (inner ℂ (X psi) (P psi) : ℂ) = inner ℂ psi (X (P psi)) := by
      rw [hX]
    have h2 : (inner ℂ (P psi) (X psi) : ℂ) = inner ℂ psi (P (X psi)) := by
      rw [hP]
    rw [h1, h2, ← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hnorm, hXpsi, hPpsi, hac, hbc, mul_one]
  rw [← key]
  ring

/-- **Heisenberg uncertainty principle** (Robertson form for the canonical commutator).

Let `ψ` be a normalized state of a complex inner product space and let `X`, `P` be
symmetric (formally self-adjoint) operators obeying the canonical commutation relation
`X (P ψ) - P (X ψ) = i ℏ ψ`. If `Δx` and `Δp` denote the standard deviations of `X` and
`P` in the state `ψ`, i.e. the norms of the centred vectors `(X - ⟨X⟩)ψ` and `(P - ⟨P⟩)ψ`,
then `Δx · Δp ≥ ℏ / 2`. -/
theorem heisenberg_uncertainty
    (X P : E →ₗ[ℂ] E) (hbar : ℝ) (psi : E) (hpsi : ‖psi‖ = 1)
    (hX : ∀ u v : E, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : E, inner ℂ (P u) v = inner ℂ u (P v))
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi)
    (Δx Δp : ℝ)
    (hΔx : Δx = ‖X psi - (inner ℂ psi (X psi) : ℂ) • psi‖)
    (hΔp : Δp = ‖P psi - (inner ℂ psi (P psi) : ℂ) • psi‖) :
    Δx * Δp ≥ hbar / 2 := by
  set u : E := X psi - (inner ℂ psi (X psi) : ℂ) • psi with hu
  set v : E := P psi - (inner ℂ psi (P psi) : ℂ) • psi with hv
  have key : (inner ℂ u v : ℂ) - inner ℂ v u = Complex.I * (hbar : ℂ) :=
    inner_comm_diff X P hbar psi hpsi hX hP hcomm
  have hsym : (inner ℂ v u : ℂ) = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm _ _).symm
  have habs : |hbar| ≤ 2 * (Δx * Δp) := by
    have h1 : ‖Complex.I * (hbar : ℂ)‖ = |hbar| := by
      simp
    have h2 : ‖(inner ℂ u v : ℂ) - inner ℂ v u‖ ≤ ‖(inner ℂ u v : ℂ)‖ + ‖(inner ℂ v u : ℂ)‖ :=
      norm_sub_le _ _
    have h3 : ‖(inner ℂ v u : ℂ)‖ = ‖(inner ℂ u v : ℂ)‖ := by
      rw [hsym, RCLike.norm_conj]
    have h4 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _
    calc |hbar| = ‖(inner ℂ u v : ℂ) - inner ℂ v u‖ := by rw [key, h1]
      _ ≤ ‖(inner ℂ u v : ℂ)‖ + ‖(inner ℂ v u : ℂ)‖ := h2
      _ = 2 * ‖(inner ℂ u v : ℂ)‖ := by rw [h3]; ring
      _ ≤ 2 * (‖u‖ * ‖v‖) := by linarith
      _ = 2 * (Δx * Δp) := by rw [hΔx, hΔp]
  have := le_abs_self hbar
  linarith

/-! ### Sharpness and non-vacuity

The hypotheses of `heisenberg_uncertainty` are satisfiable for every `ℏ ≥ 0`, and the
bound `ℏ / 2` is attained: take `X = c σₓ`, `P = c σ_y` with `c = √(ℏ/2)` on `ℂ²`, and
`ψ` the first basis vector. (The commutation relation is only required at the state `ψ`,
so a finite-dimensional model suffices.) -/

/-- The observable `c σₓ` on `ℂ²`. -/
noncomputable def pauliX (c : ℝ) : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, (c : ℂ); (c : ℂ), 0]

/-- The observable `c σ_y` on `ℂ²`. -/
noncomputable def pauliY (c : ℝ) : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, -(c : ℂ) * Complex.I; (c : ℂ) * Complex.I, 0]

/-- The state used in `heisenberg_uncertainty_sharp`. -/
noncomputable def basisState : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

lemma pauliX_isSymmetric (c : ℝ) (u v : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (pauliX c u) v = inner ℂ u (pauliX c v) := by
  have h : (Matrix.toEuclideanLin !![0, (c : ℂ); (c : ℂ), 0]).IsSymmetric := by
    rw [← Matrix.isHermitian_iff_isSymmetric]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  exact h u v

lemma pauliY_isSymmetric (c : ℝ) (u v : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (pauliY c u) v = inner ℂ u (pauliY c v) := by
  have h : (Matrix.toEuclideanLin !![0, -(c : ℂ) * Complex.I; (c : ℂ) * Complex.I, 0]).IsSymmetric := by
    rw [← Matrix.isHermitian_iff_isSymmetric]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  exact h u v

lemma norm_basisState : ‖basisState‖ = 1 := by
  simp [basisState, EuclideanSpace.norm_single]

lemma pauli_commutator (c : ℝ) :
    pauliX c (pauliY c basisState) - pauliY c (pauliX c basisState)
      = (Complex.I * ((2 * c ^ 2 : ℝ) : ℂ)) • basisState := by
  ext i
  fin_cases i
  · simp [pauliX, pauliY, basisState, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_succ]
    ring_nf
  · simp [pauliX, pauliY, basisState, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_succ]

lemma inner_basisState_pauliX (c : ℝ) : (inner ℂ basisState (pauliX c basisState) : ℂ) = 0 := by
  simp [pauliX, basisState, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]

lemma inner_basisState_pauliY (c : ℝ) : (inner ℂ basisState (pauliY c basisState) : ℂ) = 0 := by
  simp [pauliY, basisState, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]

lemma norm_centred_pauliX (c : ℝ) (hc : 0 ≤ c) :
    ‖pauliX c basisState - (inner ℂ basisState (pauliX c basisState) : ℂ) • basisState‖ = c := by
  rw [inner_basisState_pauliX, EuclideanSpace.norm_eq]
  simp [pauliX, basisState, Matrix.toLpLin_apply, Fin.sum_univ_succ]
  rw [Real.sqrt_sq hc]

lemma norm_centred_pauliY (c : ℝ) (hc : 0 ≤ c) :
    ‖pauliY c basisState - (inner ℂ basisState (pauliY c basisState) : ℂ) • basisState‖ = c := by
  rw [inner_basisState_pauliY, EuclideanSpace.norm_eq]
  simp [pauliY, basisState, Matrix.toLpLin_apply, Fin.sum_univ_succ]
  rw [Real.sqrt_sq hc]

/-- The hypotheses of `heisenberg_uncertainty` are satisfiable for every `ℏ ≥ 0`, and the
bound is sharp: there is a normalized state and a pair of symmetric operators obeying the
canonical commutation relation at that state for which `Δx · Δp = ℏ / 2`. -/
theorem heisenberg_uncertainty_sharp (hbar : ℝ) (hb : 0 ≤ hbar) :
    ∃ (X P : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (psi : EuclideanSpace ℂ (Fin 2)) (Δx Δp : ℝ),
      ‖psi‖ = 1 ∧
      (∀ u v : EuclideanSpace ℂ (Fin 2), inner ℂ (X u) v = inner ℂ u (X v)) ∧
      (∀ u v : EuclideanSpace ℂ (Fin 2), inner ℂ (P u) v = inner ℂ u (P v)) ∧
      X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi ∧
      Δx = ‖X psi - (inner ℂ psi (X psi) : ℂ) • psi‖ ∧
      Δp = ‖P psi - (inner ℂ psi (P psi) : ℂ) • psi‖ ∧
      Δx * Δp = hbar / 2 := by
  set c : ℝ := Real.sqrt (hbar / 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = hbar / 2 := Real.sq_sqrt (by linarith)
  refine ⟨pauliX c, pauliY c, basisState, c, c, norm_basisState,
    pauliX_isSymmetric c, pauliY_isSymmetric c, ?_, ?_, ?_, ?_⟩
  · have h2 : (2 * c ^ 2 : ℝ) = hbar := by rw [hcsq]; ring
    rw [pauli_commutator c, h2]
  · exact (norm_centred_pauliX c hc0).symm
  · exact (norm_centred_pauliY c hc0).symm
  · rw [← sq, hcsq]

end QPhys

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

