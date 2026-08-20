/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/

def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset ℕ, (∀ n ∈ S, n < N) →
    δ * N ≤ (S.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

