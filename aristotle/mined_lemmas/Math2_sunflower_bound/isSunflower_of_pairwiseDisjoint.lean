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

lemma isSunflower_of_pairwiseDisjoint {S : Finset (Finset α)}
    (h : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = ∅) : IsSunflower S ∅ := h

/-- The classical Erdős–Rado sunflower lemma: a family of more than `w! * (r-1)^w` sets of
size `w` contains a sunflower with `r` petals. -/
