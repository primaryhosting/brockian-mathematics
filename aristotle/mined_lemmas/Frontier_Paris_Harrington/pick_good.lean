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

lemma pick_good (c : Finset ℕ → Fin k) (n : ℕ) (A : Finset ℕ) :
    ∀ t ∈ A.powerset, ∀ q ≤ n, D c q (insert (pick c n A) t) = D c (q + 1) t :=
  (pick_exists c n A).choose_spec.2

/-- The finite set of the first `i` chosen elements. -/
