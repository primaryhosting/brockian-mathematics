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

theorem belyi_exists (S : Finset ℂ) (halg : ∀ s ∈ S, IsAlgebraic ℚ s) :
    BelyiFor (S : Set ℂ) := by
  classical
  exact belyi_of_adeg_le (S.sup adeg) S halg fun s hs => Finset.le_sup (f := adeg) hs

/-! ### The theorem -/

/-- **Belyi's theorem**, in the genus-zero (marked `ℙ¹`) model.

A finite set of points `S ⊆ ℙ¹(ℂ)` is defined over `ℚ̄` (that is, all its points are
algebraic numbers) if and only if there is a Belyi map, i.e. a nonconstant morphism
`f : ℙ¹ → ℙ¹` defined over `ℚ` which is ramified only above `{0, 1, ∞}` and which maps
the marked points `S` into `{0, 1, ∞}`.

Here `f` is realized as a polynomial `f ∈ ℚ[X]`: such a map is totally ramified over `∞`,
and the hypothesis in `IsBelyiMap` says that all of its finite critical values lie in
`{0, 1}`. -/
