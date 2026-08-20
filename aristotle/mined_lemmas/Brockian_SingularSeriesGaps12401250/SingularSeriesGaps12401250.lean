import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

namespace Brockian

/-- A finite set of shifts `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) if for every prime `p` the residues of `H` modulo `p`
do not cover all of `ℤ/pℤ`.  Equivalently, the local factor of the singular series
attached to `H` is nonzero at every prime. -/

theorem SingularSeriesGaps12401250 :
    (∀ g : ℕ, 1240 ≤ g → g ≤ 1250 → (Admissible ({0, g} : Finset ℕ) ↔ Even g)) ∧
      (Finset.Icc 1240 1250).filter (fun g => Even g) =
        ({1240, 1242, 1244, 1246, 1248, 1250} : Finset ℕ) := by
  refine ⟨fun g _ _ => admissible_pair_iff_even, ?_⟩
  decide

end Brockian

