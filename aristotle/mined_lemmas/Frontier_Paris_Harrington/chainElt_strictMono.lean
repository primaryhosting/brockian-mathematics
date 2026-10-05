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

theorem chainElt_strictMono : StrictMono (chainElt U D k) :=
  strictMono_nat_of_lt_succ (chainElt_lt_succ U D k hU hD)

omit hU hD in
