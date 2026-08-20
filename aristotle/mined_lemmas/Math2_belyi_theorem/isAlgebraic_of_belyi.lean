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

theorem isAlgebraic_of_belyi {f : ℚ[X]} (hf : IsBelyiMap f) {s : ℂ}
    (hs : aeval s f ∈ ({0, 1} : Set ℂ)) : IsAlgebraic ℚ s := by
  obtain ⟨hdeg, -⟩ := hf
  rcases hs with h | h
  · exact ⟨f, fun hf0 => by simp [hf0] at hdeg, h⟩
  · refine ⟨f - 1, ?_, by simp [map_sub, Set.mem_singleton_iff.mp h]⟩
    intro h0
    have : f = 1 := by linear_combination (norm := ring_nf) h0
    simp [this] at hdeg

/-! ### Belyi's pushing construction -/

/-- Evaluating a rational polynomial at a rational point, viewed in `ℂ`. -/
