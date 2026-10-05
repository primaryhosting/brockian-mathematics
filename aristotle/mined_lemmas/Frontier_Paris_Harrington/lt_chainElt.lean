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

theorem lt_chainElt (n : ℕ) : ∀ y ∈ chain U D k n, y < chainElt U D k n :=
  (chainElt_mem_goodSet U D k hU hD n).1

