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

/-
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The set of coprime residues mod `9` in `range 9`. -/

lemma coprime_filter_nine :
    ((Finset.range 9).filter fun i => Nat.Coprime 9 i) = ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
  decide

/-- The sum of the primitive `9`-th roots of unity, written as a sum of powers of a fixed
primitive root, vanishes. -/
