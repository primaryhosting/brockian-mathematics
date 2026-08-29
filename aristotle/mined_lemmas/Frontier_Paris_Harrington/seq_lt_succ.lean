import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

namespace ParisHarrington

open Filter

/-- A fixed ultrafilter on `ℕ` refining the filter `atTop`; in particular every cofinite
set belongs to it. -/

lemma seq_lt_succ (c : Finset ℕ → Fin k) (n i : ℕ) : seq c n i < seq c n (i + 1) := by
  have hmem : seq c n i ∈ chosen c n (i + 1) := by
    rw [chosen]
    exact Finset.mem_insert_self _ _
  exact pick_gt c n (chosen c n (i + 1)) _ hmem

