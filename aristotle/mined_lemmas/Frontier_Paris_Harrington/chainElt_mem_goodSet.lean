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

theorem chainElt_mem_goodSet (n : ℕ) :
    chainElt U D k n ∈ goodSet D k (chain U D k n) :=
  Nat.sInf_mem (Ultrafilter.nonempty_of_mem (goodSet_mem U D k hU hD _))

