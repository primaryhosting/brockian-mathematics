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

theorem no_local_model_for_quantum_hardy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Bool → Ω → Bool)
    (h₁ : μ {ω | A false ω = true ∧ B true ω = false}
            = ENNReal.ofReal (qprob false true true false))
    (h₂ : μ {ω | A true ω = false ∧ B false ω = true}
            = ENNReal.ofReal (qprob true false false true))
    (h₃ : μ {ω | A true ω = true ∧ B true ω = true}
            = ENNReal.ofReal (qprob true true true true))
    (h₄ : μ {ω | A false ω = true ∧ B false ω = true}
            = ENNReal.ofReal (qprob false false true true)) :
    False := by
  refine hardy_paradox μ A B ?_ ?_ ?_ ?_
  · rw [h₁, qprob_A₁_one_B₂_zero]; simp
  · rw [h₂, qprob_A₂_zero_B₁_one]; simp
  · rw [h₃, qprob_A₂_one_B₂_one]; simp
  · rw [h₄, qprob_first_first]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num

end QI

