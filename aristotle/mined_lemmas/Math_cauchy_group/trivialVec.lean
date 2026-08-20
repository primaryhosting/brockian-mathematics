import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-!
## McKay's proof of Cauchy's theorem

The whole argument is developed from scratch here: we consider the set of lists of length `p`
of elements of `G` whose product is `1`, let the cyclic group `ZMod p` act on it by rotation,
and compare the cardinality of this set (which is `|G| ^ (p-1)`, divisible by `p`) with the
cardinality of the set of fixed points (constant lists `[g, …, g]` with `g ^ p = 1`) modulo `p`.
-/

/-- The set of lists of length `p` of elements of `G` whose product is `1`. -/

def trivialVec (G : Type*) [Group G] (p : ℕ) : ProdOne G p :=
  ⟨List.replicate p 1, by simp, by simp⟩

