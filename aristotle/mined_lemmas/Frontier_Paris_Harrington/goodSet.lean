import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

def goodSet {r : ℕ} (D : ℕ → Finset ℕ → Fin r) (k : ℕ) (T : Finset ℕ) : Set ℕ :=
  {x | (∀ y ∈ T, y < x) ∧ ∀ s ⊆ T, ∀ i, i + s.card + 1 = k → D i (insert x s) = D (i + 1) s}

