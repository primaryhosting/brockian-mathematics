import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Filter Set

open Classical in
/-- Choice of an element of a set of naturals (junk value `0` when empty). -/

noncomputable def ramseySets (g : ℕ → ℕ → Bool) (c : Bool) (A : Set ℕ) : ℕ → Set ℕ
  | 0 => A
  | k + 1 =>
      {m ∈ ramseySets g c A k |
        pickElem (ramseySets g c A k) < m ∧ g (pickElem (ramseySets g c A k)) m = c}

/-- The monochromatic sequence itself. -/
