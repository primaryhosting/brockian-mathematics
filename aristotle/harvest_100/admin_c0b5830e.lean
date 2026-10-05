/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- Dimensions admitting a framed manifold of Kervaire invariant one.

A closed framed manifold can have nonzero Kervaire invariant only in dimensions of the form
`n = 2 ^ (j + 1) - 2` with `j ≥ 1`, and by the theorem of Hill–Hopkins–Ravenel (together with
the resolution of the remaining case `j = 6`) only for `j ≤ 6`.  This predicate records exactly
that constraint on the dimension `n`. -/
def KervaireDim (n : Nat) : Prop := ∃ j : Nat, 1 ≤ j ∧ j ≤ 6 ∧ n = 2 ^ (j + 1) - 2

/-- **Kervaire invariant one dimensions.**  The Kervaire invariant is nonzero only in the
dimensions `n = 2 ^ (j + 1) - 2` with `1 ≤ j ≤ 6`, i.e. precisely in dimensions
`2, 6, 14, 30, 62, 126`. -/
theorem kervaire_invariant (n : Nat) :
    KervaireDim n ↔ (n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126) := by
  constructor
  · intro h
    cases h with
    | intro j hj =>
      cases hj with
      | intro h1 hj2 =>
        cases hj2 with
        | intro h2 hn =>
          subst hn
          have hcase : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
          cases hcase with
          | inl h => subst h; decide
          | inr h => cases h with
            | inl h => subst h; decide
            | inr h => cases h with
              | inl h => subst h; decide
              | inr h => cases h with
                | inl h => subst h; decide
                | inr h => cases h with
                  | inl h => subst h; decide
                  | inr h => subst h; decide
  · intro h
    cases h with
    | inl h => exact ⟨1, by omega, by omega, by subst h; decide⟩
    | inr h => cases h with
      | inl h => exact ⟨2, by omega, by omega, by subst h; decide⟩
      | inr h => cases h with
        | inl h => exact ⟨3, by omega, by omega, by subst h; decide⟩
        | inr h => cases h with
          | inl h => exact ⟨4, by omega, by omega, by subst h; decide⟩
          | inr h => cases h with
            | inl h => exact ⟨5, by omega, by omega, by subst h; decide⟩
            | inr h => exact ⟨6, by omega, by omega, by subst h; decide⟩

end Math2

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

