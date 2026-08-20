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

theorem belyi_mono {S T : Set ℂ} (h : S ⊆ T) (hT : BelyiFor T) : BelyiFor S := by
  obtain ⟨f, hf, hfT⟩ := hT
  exact ⟨f, hf, fun s hs => hfT s (h hs)⟩

/-! ### The easy direction -/

