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

theorem generator_comm (U : ℝ → A) (B : A) (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hone : U 0 = 1) (hB : ∀ t, HasDerivAt U (U t * B) t) (t : ℝ) : U t * B = B * U t := by
  have h1 : HasDerivAt (fun r => U (t + r)) (U t * B) 0 := by
    have := (hB 0).const_mul (U t)
    rw [hone, one_mul] at this
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hgroup t r)
  have h2 : HasDerivAt (fun r => U (t + r)) (B * U t) 0 := by
    have := (hB 0).mul_const (U t)
    rw [hone, one_mul] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    rw [add_comm t r, hgroup r t]
  exact h1.unique h2

end BanachAlgebra

section Generator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- If a one-parameter unitary group has derivative `B` at `0` (in the strong sense),
then `B` is skew-adjoint. -/
