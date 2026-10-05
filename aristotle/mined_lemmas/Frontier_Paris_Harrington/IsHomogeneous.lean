/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- A finite set `H` of natural numbers is *relatively large* when it has a least element `a`
and its cardinality is at least `a`. -/

def IsHomogeneous (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (H : Finset ℕ) (i : Fin k) : Prop :=
  ∀ s ⊆ H, s.card = n → c s = i

/-- **Infinite Ramsey theorem** for `n`-element subsets of `ℕ` and `k` colours: every infinite
set of naturals has an infinite subset all of whose `n`-element subsets get the same colour. -/
