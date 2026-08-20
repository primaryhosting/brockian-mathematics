/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Belyi's theorem is formalized in its genus-zero (polynomial) form, which is the arithmetic heart
of the theorem: the "curve" is the projective line together with a finite set `S` of marked
complex points, and a Belyi map is given by a polynomial `f ∈ ℚ[X]` — viewed as a map
`ℙ¹ → ℙ¹` defined over `ℚ` for which `∞` is totally ramified over `∞`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` (i.e. all elements of
`S` are algebraic over `ℚ`) if and only if there is a nonconstant such `f` which maps `S` into
`{0, 1}` and all of whose critical values lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`.

The easy direction is elementary. The hard direction is Belyi's algorithm, carried out here in
two stages:

* `Math2.stageA`: composing with minimal polynomials, one finds a nonconstant `f ∈ ℚ[X]` for
  which the images of the marked points and all critical values are rational. Termination is
  measured by `Math2.muA`, a sum of factorials of the degrees of the algebraic numbers involved.
* `Math2.stageB`: a finite set of rationals is collapsed into `{0, 1}` by repeatedly composing
  with the polynomials `c · x^m (1-x)^n` (after an affine change of coordinates), each step
  strictly decreasing the number of relevant rational values.
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

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Critical points and critical values -/

/-- The critical points in `ℂ` of a polynomial with rational coefficients. -/

lemma exists_belyi_three {a b c : ℚ} (hab : a < b) (hbc : b < c) :
    ∃ P : ℚ[X], 1 ≤ P.natDegree ∧ P.eval a = 0 ∧ P.eval c = 0 ∧ P.eval b = 1 ∧
      (∀ w : ℂ, aeval w (derivative P) = 0 → aeval w P = 0 ∨ aeval w P = 1) := by
  have hca : (0 : ℚ) < c - a := by linarith
  set lam : ℚ := (b - a) / (c - a) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; apply div_pos <;> linarith
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hca]; linarith
  obtain ⟨B, _, hB0, hBone, hBlam, hBc⟩ := exists_belyi_base hlam0 hlam1
  set A : ℚ[X] := C (c - a)⁻¹ * (X - C a) with hA
  have hAa : A.eval a = 0 := by simp [hA]
  have hAc : A.eval c = 1 := by
    simp only [hA, eval_mul, eval_C, eval_sub, eval_X]
    field_simp
  have hAb : A.eval b = lam := by
    simp only [hA, eval_mul, eval_C, eval_sub, eval_X, hlam]
    field_simp
  refine ⟨B.comp A, ?_, ?_, ?_, ?_, ?_⟩
  · refine one_le_natDegree_of_eval_ne (x := a) (y := b) ?_
    rw [eval_comp, eval_comp, hAa, hAb, hB0, hBlam]
    norm_num
  · rw [eval_comp, hAa, hB0]
  · rw [eval_comp, hAc, hBone]
  · rw [eval_comp, hAb, hBlam]
  · intro w hw
    rw [derivative_comp, map_mul, mul_eq_zero] at hw
    have hdA : derivative A = C (c - a)⁻¹ := by simp [hA]
    rcases hw with hw | hw
    · rw [hdA] at hw
      simp only [aeval_C, eq_ratCast, Rat.cast_eq_zero, inv_eq_zero, sub_eq_zero] at hw
      exact absurd hw (by intro h; rw [h] at hca; simp at hca)
    · rw [aeval_comp] at hw
      rw [aeval_comp]
      exact hBc _ hw

/-! ## Stage B: collapsing a finite set of rational values to `{0,1}` -/

