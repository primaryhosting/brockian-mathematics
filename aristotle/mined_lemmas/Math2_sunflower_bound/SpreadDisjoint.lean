/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

def SpreadDisjoint (rho : ℕ → ℕ → ℝ) : Prop :=
  ∀ (p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ S : Finset (Finset α), (∀ A ∈ S, A.card = k) →
    IsSpread S k (rho p k) → (rho p k) ^ k ≤ (S.card : ℝ) →
    ∃ D ⊆ S, D.card = p ∧ ∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B

/-- A family of at least `p` pairwise disjoint sets is a sunflower with empty core. -/
