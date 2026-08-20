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

def BelyiFor (S : Set ℂ) : Prop :=
  ∃ f : ℚ[X], IsBelyiMap f ∧ ∀ s ∈ S, aeval s f ∈ ({0, 1} : Set ℂ)

/-- The degree over `ℚ` of a complex number (junk value `0` for transcendentals). -/
