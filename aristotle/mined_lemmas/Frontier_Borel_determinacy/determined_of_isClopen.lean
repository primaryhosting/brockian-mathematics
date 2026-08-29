/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

theorem determined_of_isClopen [TopologicalSpace A] [DiscreteTopology A] {S : Set (ℕ → A)}
    (hS : IsClopen S) : Determined S :=
  determined_of_isOpen hS.2

end GaleStewart

/-! ## Coverings and the transfer of determinacy -/

/-- A *covering* of the game on `A` by the game on `B` (Martin).  It consists of a map `push`
sending plays of the `B`-game to plays of the `A`-game together with maps lifting strategies of
the `B`-game to strategies of the `A`-game, in such a way that every play following a lifted
strategy is the image of a play following the original strategy. -/
structure Covering (A : Type u) (B : Type u) where
  push : (ℕ → B) → (ℕ → A)
  liftI : Strategy B → Strategy A
  liftII : Strategy B → Strategy A
  liftI_spec : ∀ (σ : Strategy B) (x : ℕ → A), ConsistentI (liftI σ) x →
    ∃ y, ConsistentI σ y ∧ push y = x
  liftII_spec : ∀ (τ : Strategy B) (x : ℕ → A), ConsistentII (liftII τ) x →
    ∃ y, ConsistentII τ y ∧ push y = x

/-- The identity covering: it shows that the notion of covering is not vacuous. -/
