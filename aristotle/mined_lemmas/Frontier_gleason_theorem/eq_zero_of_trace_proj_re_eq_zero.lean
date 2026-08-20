/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28's module system forbids a `/-!` module docstring before `import`;
-- the header above is therefore a plain block comment and is repeated below.)

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *quantum measure* on a finite dimensional complex Hilbert space `ℂⁿ` is a map `μ` from the
orthogonal projections to `ℝ` which is nonnegative, finitely additive on orthogonal pairs, and
normalized (`μ 1 = 1`).  Gleason's theorem says that in dimension at least three every such `μ`
is given by the Born rule `μ P = Tr(ρ P)` for a unique density operator `ρ`.

This file contains:

* `Frontier.QuantumMeasure`, `Frontier.IsDensity`, `Frontier.Represents`: the formalized
  statement ingredients;
* `Frontier.born_rule_quantumMeasure`: every density operator gives a quantum measure;
* `Frontier.density_of_positive_linear`: a linear functional on matrices that is nonnegative
  on projections and normalized is the trace against a density operator;
* `Frontier.density_unique`: the density operator representing a measure is unique;
* `Frontier.gleason_theorem`: the Lean-checked reduction of Gleason's theorem to the linearity
  of the frame function (the analytic heart of the classical proof);
* `Frontier.gleason_fails_in_dimension_two`: an explicit quantum measure on the projections of
  `ℂ²` that is represented by no operator, showing that the dimension hypothesis is necessary.
-/

open Matrix Complex
open scoped ComplexOrder

namespace Frontier

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal projection: a Hermitian idempotent matrix. -/

lemma eq_zero_of_trace_proj_re_eq_zero {D : Matrix n n ℂ} (hD : D.IsHermitian)
    (h : ∀ P, IsProjection P → (D * P).trace.re = 0) : D = 0 := by
  have hdiag : ∀ i : n, D i i = 0 := by
    intro i
    have h1 := h _ (isProjection_single_diag i)
    rw [trace_mul_single] at h1
    simp only [one_mul] at h1
    have h2 : (starRingEnd ℂ) (D i i) = D i i := by
      have := congrFun (congrFun hD i) i
      simpa [Matrix.conjTranspose_apply] using this
    have h3 : (D i i).im = 0 := by
      simpa using (Complex.conj_eq_iff_im.mp h2)
    exact Complex.ext h1 h3
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [hdiag i]
  have hconj : (starRingEnd ℂ) (D i j) = D j i := by
    have := congrFun (congrFun hD j) i
    simpa [Matrix.conjTranspose_apply] using this
  have h1 := h _ (isProjection_pairProj hij)
  have h2 := h _ (isProjection_pairProjI hij)
  rw [pairProj, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, trace_mul_single,
    trace_mul_single, trace_mul_single, trace_mul_single, hdiag i, hdiag j] at h1
  rw [pairProjI, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    trace_mul_single, trace_mul_single, trace_mul_single, trace_mul_single, hdiag i,
    hdiag j] at h2
  have hre : (D i j).re = 0 := by
    have hz : ((2 : ℂ)⁻¹ * (1 * 0 + 1 * D j i + 1 * D i j + 1 * 0)).re = 0 := h1
    rw [← hconj] at hz
    simp [Complex.mul_re, Complex.add_re, Complex.inv_re] at hz
    linarith
  have him : (D i j).im = 0 := by
    have hz : ((2 : ℂ)⁻¹ * (1 * 0 + -Complex.I * (1 * D j i) + Complex.I * (1 * D i j)
      + 1 * 0)).re = 0 := h2
    rw [← hconj] at hz
    simp [Complex.mul_re, Complex.add_re, Complex.inv_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] at hz
    linarith
  simpa using Complex.ext hre him

/-- **Uniqueness in Gleason's theorem.** A quantum measure determines its density operator. -/
