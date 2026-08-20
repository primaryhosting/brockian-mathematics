/-
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

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (· ∈ A)).card

open scoped Classical in
/-- The upper (asymptotic) density of a set of naturals. -/
