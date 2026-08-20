import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The *local constellation count* of the shift pattern (constellation) `h : Fin k → ℤ`
relative to a set `S` of integers, counted over the window `I`:
the number of `x ∈ I` such that all the shifted points `x + h i` lie in `S`. -/

def constLocalCount {k : ℕ} (S I : Finset ℤ) (h : Fin k → ℤ) : ℕ :=
  (I.filter (fun x => ∀ i : Fin k, x + h i ∈ S)).card

/-- `k = 1`: the local count of a one-point constellation. -/
