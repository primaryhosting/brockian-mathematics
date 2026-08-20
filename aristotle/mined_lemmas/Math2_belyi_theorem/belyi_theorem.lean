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

theorem belyi_theorem (S : Finset ℂ) :
    (∀ z ∈ S, IsAlgebraic ℚ z) ↔
      ∃ f : ℚ[X], 1 ≤ f.natDegree ∧
        (∀ z ∈ S, aeval z f = 0 ∨ aeval z f = 1) ∧
        (∀ w : ℂ, aeval w (derivative f) = 0 → aeval w f = 0 ∨ aeval w f = 1) := by
  constructor
  · intro hS
    obtain ⟨f, T, hf1, hfS, hfC⟩ := stageA (muA S) S hS le_rfl
    obtain ⟨g, hg1, hgT, hgC⟩ := stageB (insert (0 : ℚ) (insert 1 T)).card T le_rfl
    refine ⟨g.comp f, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_comp]
      calc 1 = 1 * 1 := by norm_num
        _ ≤ g.natDegree * f.natDegree := Nat.mul_le_mul hg1 hf1
    · intro z hz
      obtain ⟨t, htT, ht⟩ := hfS z hz
      rw [Polynomial.aeval_comp, ht, aeval_ratCast]
      rcases hgT t htT with h | h <;> simp [h]
    · intro w hw
      rw [Polynomial.derivative_comp, map_mul, mul_eq_zero] at hw
      rcases hw with hw | hw
      · obtain ⟨t, htT, ht⟩ := hfC w hw
        rw [Polynomial.aeval_comp, ht, aeval_ratCast]
        rcases hgT t htT with h | h <;> simp [h]
      · rw [Polynomial.aeval_comp] at hw
        rw [Polynomial.aeval_comp]
        exact hgC _ hw
  · rintro ⟨f, hf1, hfS, -⟩ z hz
    have hf0 : f ≠ 0 := fun h => by simp [h] at hf1
    rcases hfS z hz with h | h
    · exact ⟨f, hf0, h⟩
    · refine ⟨f - 1, ?_, ?_⟩
      · intro h1
        have : f = 1 := by linear_combination (norm := ring_nf) h1
        rw [this] at hf1
        simp at hf1
      · simp [h]

end

end Math2

