import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

/-- The Gibbs entropy of a (finite) probability vector `p`, given by `-∑ pᵢ log pᵢ`. -/

lemma convex_nonneg (n : ℕ) : Convex ℝ {p : Fin n → ℝ | ∀ i, 0 ≤ p i} := by
  intro p hp q hq a b ha hb _ i
  have h₁ : 0 ≤ a * p i := mul_nonneg ha (hp i)
  have h₂ : 0 ≤ b * q i := mul_nonneg hb (hq i)
  simpa using add_nonneg h₁ h₂

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector.**
Stated on the convex set of all nonnegative vectors, which contains the probability simplex. -/
