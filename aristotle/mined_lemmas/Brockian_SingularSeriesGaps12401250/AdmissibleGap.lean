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

/-- A gap `h` is *admissible* when the pair `{0, h}` is an admissible 2-tuple in the
Hardy–Littlewood sense: for every prime `p`, the reductions of `0` and `h` modulo `p`
do not cover all residue classes mod `p`.  This is exactly the condition under which the
singular series `𝔖(h)` attached to the gap `h` is nonzero. -/

def AdmissibleGap (h : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (({0, h} : Finset ℕ).image (· % p)).card < p

/-- A gap `h` is admissible exactly when it is even (the only obstruction comes from `p = 2`). -/
