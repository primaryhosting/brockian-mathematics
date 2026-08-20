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

lemma star_linear_single {φ : Matrix n n ℂ →ₗ[ℂ] ℂ}
    (hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P) (i j : n) :
    star (φ (Matrix.single i j 1)) = φ (Matrix.single j i 1) := by
  have hdiag : ∀ k : n, (φ (Matrix.single k k 1)).im = 0 := by
    intro k
    have := hpos _ (isProjection_single_diag k)
    simpa using ((Complex.le_def.mp this).2).symm
  rcases eq_or_ne i j with rfl | hij
  · exact Complex.ext rfl (by simp [hdiag i])
  set z : ℂ := φ (Matrix.single i j 1) with hz
  set w : ℂ := φ (Matrix.single j i 1) with hw
  -- first test vector: `e i + e j`
  set v₁ : n → ℂ := fun a => if a = i then 1 else if a = j then 1 else 0 with hv₁
  set v₂ : n → ℂ := fun a => if a = i then 1 else if a = j then Complex.I else 0 with hv₂
  have hm₁ : Matrix.vecMulVec v₁ (star v₁)
      = Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have hm₂ : Matrix.vecMulVec v₂ (star v₂)
      = Matrix.single i i 1 + (-Complex.I) • Matrix.single i j (1 : ℂ)
        + Complex.I • Matrix.single j i (1 : ℂ) + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have h₁ := linear_vecMulVec_nonneg hpos v₁
  have h₂ := linear_vecMulVec_nonneg hpos v₂
  rw [hm₁] at h₁
  rw [hm₂] at h₂
  have e₁ : φ (Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1
      + Matrix.single j j 1)
      = φ (Matrix.single i i 1) + z + w + φ (Matrix.single j j 1) := by
    rw [map_add, map_add, map_add, hz, hw]
  have e₂ : φ (Matrix.single i i 1 + (-Complex.I) • Matrix.single i j (1 : ℂ)
      + Complex.I • Matrix.single j i (1 : ℂ) + Matrix.single j j 1)
      = φ (Matrix.single i i 1) + (-Complex.I) * z + Complex.I * w + φ (Matrix.single j j 1) := by
    rw [map_add, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hz, hw]
  rw [e₁] at h₁
  rw [e₂] at h₂
  have him₁ : z.im + w.im = 0 := by
    have := ((Complex.le_def.mp h₁).2).symm
    simp [Complex.add_im, hdiag i, hdiag j] at this
    linarith [this]
  have him₂ : w.re - z.re = 0 := by
    have := ((Complex.le_def.mp h₂).2).symm
    simp [Complex.add_im, Complex.mul_im, hdiag i, hdiag j] at this
    linarith [this]
  refine Complex.ext ?_ ?_
  · simpa using by linarith [him₂]
  · simp only [Complex.star_def, Complex.conj_im]
    linarith [him₁]

