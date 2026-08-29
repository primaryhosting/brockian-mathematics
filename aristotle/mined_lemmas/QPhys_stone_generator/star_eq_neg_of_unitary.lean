/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate

namespace QPhys

section Strong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a finite-dimensional space, strong continuity of a family of operators implies
continuity in the operator norm. -/

theorem star_eq_neg_of_unitary (U : ℝ → (E →L[ℂ] E)) (B : E →L[ℂ] E) (hone : U 0 = 1)
    (hunitary : ∀ t x y, inner ℂ (U t x) (U t y) = (inner ℂ x y : ℂ))
    (hB : ∀ x, HasDerivAt (fun t => U t x) (B x) 0) : star B = -B := by
  have key : ∀ x y : E, (inner ℂ x (B y) : ℂ) + inner ℂ (B x) y = 0 := by
    intro x y
    have hd : HasDerivAt (fun t => (inner ℂ (U t x) (U t y) : ℂ))
        (inner ℂ (U 0 x) (B y) + inner ℂ (B x) (U 0 y)) 0 := (hB x).inner ℂ (hB y)
    have hconst : HasDerivAt (fun t : ℝ => (inner ℂ (U t x) (U t y) : ℂ)) 0 0 := by
      simp only [hunitary]
      exact hasDerivAt_const _ _
    have h0 := hd.unique hconst
    simpa [hone] using h0
  ext x
  refine ext_inner_right ℂ ?_
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have := key x y
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left]
  linear_combination (norm := module) this

end Generator

/-- **Stone's theorem** (bounded / finite-dimensional case).

A strongly continuous one-parameter unitary group `U` on a finite-dimensional complex
Hilbert space has a self-adjoint generator `H`: for every state `x` the orbit `t ↦ U t x`
solves the Schrödinger equation `d/dt (U t x) = -i • H (U t x)`, and `H` commutes with
the group. -/
