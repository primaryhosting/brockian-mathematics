/-
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

/-- The local count of a constellation (`k`-tuple of shifts) `H` modulo `p`: the number of
residues `n` such that none of the shifted values `n + h`, `h ∈ H`, is divisible by `p`.
This is the quantity `p - ν_H(p)` appearing in the singular series of the Hardy–Littlewood
prime `k`-tuple heuristic. -/

noncomputable def constellationLocalCount (p : ℕ) [NeZero p] (H : Finset (ZMod p)) : ℕ :=
  (Finset.univ.filter (fun n : ZMod p => ∀ h ∈ H, n + h ≠ 0)).card

/-- The set of residues avoiding all shifts in `H` is the complement of `-H`. -/
