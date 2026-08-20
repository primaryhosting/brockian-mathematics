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

theorem belyi_comp (g : ℚ[X]) (hg : 0 < g.natDegree) (S T : Set ℂ)
    (hcrit : ∀ z : ℂ, aeval z (derivative g) = 0 → aeval z g ∈ T)
    (hS : ∀ s ∈ S, aeval s g ∈ T) (hT : BelyiFor T) : BelyiFor S := by
  obtain ⟨f, ⟨hfdeg, hfcrit⟩, hfT⟩ := hT
  refine ⟨f.comp g, ⟨?_, ?_⟩, ?_⟩
  · rw [natDegree_comp]; positivity
  · intro z hz
    rw [derivative_comp, map_mul, mul_eq_zero] at hz
    rw [aeval_comp]
    rcases hz with h | h
    · exact hfT _ (hcrit z h)
    · rw [aeval_comp] at h
      exact hfcrit _ h
  · intro s hs
    rw [aeval_comp]
    exact hfT _ (hS s hs)

