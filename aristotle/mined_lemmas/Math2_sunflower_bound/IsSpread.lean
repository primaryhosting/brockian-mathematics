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

def IsSpread (S : Finset (Finset α)) (k : ℕ) (r : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty → ((S.filter (fun A => T ⊆ A)).card : ℝ) ≤ r ^ (k - T.card)

/-- The *spread-to-disjoint* property of a threshold function `rho`: every `rho p k`-spread
family of `k`-sets with at least `(rho p k) ^ k` members contains `p` pairwise disjoint sets. -/
