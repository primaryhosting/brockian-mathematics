import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

/-- The conditional probability of the event `E` given the (information) cell `C`,
computed from the weight function `p`. -/

noncomputable def condProb {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (E C : Finset Ω) : ℝ :=
  (∑ y ∈ C ∩ E, p y) / (∑ y ∈ C, p y)

/-- Key aggregation lemma: if a finite set `M` is closed under the information map `I`
(i.e. it is a union of cells of the partition induced by `I`), and every cell of a point of `M`
assigns the event `E` conditional probability `q` (in multiplicative form), then `M` itself
assigns `E` conditional probability `q` (in multiplicative form). -/
