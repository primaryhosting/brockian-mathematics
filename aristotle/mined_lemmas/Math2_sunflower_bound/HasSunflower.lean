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

def HasSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ S ⊆ F, S.card = r ∧ ∃ c, IsSunflower S c

/-- A family of pairwise disjoint sets is a sunflower with empty core. -/
