import Mathlib

/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
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

namespace QI

open MeasureTheory

/-! ## Hardy's paradox for local hidden-variable models

A local hidden-variable model for a bipartite experiment with two binary settings and two
binary outcomes per party consists of a probability space `Ω` (the hidden variables) together
with outcome functions `A x ω` for Alice and `B y ω` for Bob.  *Locality* is encoded in the
types: Alice's outcome depends only on her own setting `x` and the hidden variable `ω`, never
on Bob's setting `y`, and symmetrically for Bob.

Hardy's argument shows that no such model can satisfy the four *Hardy conditions*:

* `A₁ = 1` implies `B₂ = 1` (almost surely),
* `B₁ = 1` implies `A₂ = 1` (almost surely),
* `A₂ = 1` and `B₂ = 1` never happen together (almost surely),
* yet `A₁ = 1` and `B₁ = 1` happen with nonzero probability.

Here the setting `false` stands for the first measurement and `true` for the second one, and
the outcome `true` stands for the outcome "1".
-/

/-- **Hardy's paradox.**  There is no local hidden-variable model satisfying the four Hardy
conditions.  Locality is built into the statement: Alice's outcome `A x ω` does not depend on
Bob's setting and Bob's outcome `B y ω` does not depend on Alice's setting.

The three "impossible" events have probability zero, while the event `A₁ = 1 ∧ B₁ = 1` has
nonzero probability; but that event is contained in the union of the three null events, a
contradiction.  No measurability assumptions are needed. -/

noncomputable def qvec : Bool → Bool → Fin 2 → ℂ
  | false, true  => ![1 / Real.sqrt 2, 1 / Real.sqrt 2]
  | false, false => ![1 / Real.sqrt 2, -(1 / Real.sqrt 2)]
  | true,  true  => ![1, 0]
  | true,  false => ![0, 1]

/-- The Hardy state `ψ = (|01⟩ + |10⟩ - |11⟩)/√3`, written as its coefficient matrix. -/
