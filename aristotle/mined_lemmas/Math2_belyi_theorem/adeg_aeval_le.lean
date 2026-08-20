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

theorem adeg_aeval_le {β : ℂ} (hβ : IsAlgebraic ℚ β) (p : ℚ[X]) :
    adeg (aeval β p) ≤ adeg β := by
  have hi : IsIntegral ℚ β := hβ.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮β⟯ := IntermediateField.adjoin.finiteDimensional hi
  have hmem : aeval β p ∈ ℚ⟮β⟯ :=
    (IntermediateField.algebra_adjoin_le_adjoin ℚ {β}) (aeval_mem_adjoin_singleton ℚ β)
  have hle : ℚ⟮aeval β p⟯ ≤ ℚ⟮β⟯ := IntermediateField.adjoin_simple_le_iff.mpr hmem
  unfold adeg
  rw [← IntermediateField.adjoin.finrank hi,
    ← IntermediateField.adjoin.finrank (isIntegral_aeval hβ p)]
  exact IntermediateField.finrank_le_of_le_right hle

/-- Base case of the descent: points of degree at most one, i.e. rational points. -/
