/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

namespace Brockian

/-- The *local count* `ν_p(H)` of a finite tuple `H` of integers at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/

theorem admissible_zero_two_six : Admissible ({0, 2, 6} : Finset ℤ) := by
  have hcard : ({0, 2, 6} : Finset ℤ).card = 3 := by decide
  rw [ConstellationLocalCountK3 _ hcard]
  constructor
  · show (({0, 2, 6} : Finset ℤ).image (fun n : ℤ => (n : ZMod 2))).card < 2
    norm_num [Finset.image_insert, localCount]
  · show (({0, 2, 6} : Finset ℤ).image (fun n : ℤ => (n : ZMod 3))).card < 3
    norm_num [Finset.image_insert, localCount]
    decide

/-- The triple `{0, 2, 4}` is *not* admissible: it covers every residue class mod `3`. -/
