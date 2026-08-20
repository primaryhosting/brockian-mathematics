import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyi_zero_one (S : Set ℂ) (h : ∀ s ∈ S, s ∈ ({0, 1} : Set ℂ)) : BelyiFor S := by
  refine ⟨X, ⟨by simp, ?_⟩, ?_⟩
  · intro z hz; simp at hz
  · intro s hs; simpa using h s hs

/-- Belyi's theorem for a finite set of rationals contained in `[0,1]`, by induction on the
number of points different from `0` and `1`. -/
