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

def IsBelyiMap (f : ℚ[X]) : Prop :=
  0 < f.natDegree ∧ ∀ z : ℂ, aeval z (derivative f) = 0 → aeval z f ∈ ({0, 1} : Set ℂ)

/-- `BelyiFor S` says that there is a Belyi map sending every point of `S` into the
branch locus `{0, 1, ∞}` (concretely, into `{0,1}`). -/
