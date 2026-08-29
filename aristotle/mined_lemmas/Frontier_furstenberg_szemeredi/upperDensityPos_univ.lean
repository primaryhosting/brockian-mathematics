import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`, i.e. there are `a` and a positive
common difference `d` with `a, a + d, …, a + (k-1) * d` all in `A`. -/

lemma upperDensityPos_univ : UpperDensityPos Set.univ :=
  ⟨1, one_pos, fun N => ⟨N, le_rfl, by simp [prefixCard]⟩⟩

end Basic

/-- **Reduction**: the finitary density form of Szemerédi's theorem implies the infinitary
statement about sets of positive upper density. -/
