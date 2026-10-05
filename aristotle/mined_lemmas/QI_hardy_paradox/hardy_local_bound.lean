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

/-!
## Setting

Hardy's nonlocality argument.  Two spacelike separated parties, Alice and Bob, each
choose one of two measurement settings and record a `Bool` outcome.  A *local
hidden-variable* (local realistic) model consists of

* a space `Λ` of hidden variables carrying a probability measure `μ`,
* response functions `a₁, a₂ : Λ → Bool` for Alice's two settings and
  `b₁, b₂ : Λ → Bool` for Bob's two settings,

Alice's outcome depending only on her own setting and on `λ`, and likewise for Bob
(this is exactly locality plus outcome determinism; the functions are *not* assumed
measurable, all statements are about the outer measure `μ`).

The four *Hardy conditions* are

* `μ {λ | a₂ λ ∧ b₂ λ} > 0`  (the "Hardy event" happens in a nonzero fraction of runs),
* `μ {λ | a₁ λ ∧ b₂ λ} = 0`,
* `μ {λ | a₂ λ ∧ b₁ λ} = 0`,
* `μ {λ | ¬ a₁ λ ∧ ¬ b₁ λ} = 0`.

Hardy's argument shows these four are jointly contradictory: no inequality is needed,
a single run of the Hardy event already refutes local realism.
-/

section LocalModel

variable {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ) (a₁ a₂ b₁ b₂ : Λ → Bool)

/-- The "Hardy event": Alice's second setting and Bob's second setting both yield `true`. -/

theorem hardy_local_bound :
    μ (hardyEvent a₂ b₂) ≤
      μ {l | a₁ l = true ∧ b₂ l = true} +
      μ {l | a₂ l = true ∧ b₁ l = true} +
      μ {l | a₁ l = false ∧ b₁ l = false} := by
  refine le_trans (measure_mono (hardyEvent_subset a₁ a₂ b₁ b₂)) ?_
  exact le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)

/-- **Hardy's paradox.**  No local hidden-variable model can reproduce the four Hardy
conditions: if the three "impossible" events have probability zero, then the Hardy
event has probability zero as well, so it cannot occur in a nonzero fraction of runs.
Hence a nonzero fraction of runs witnesses the violation of local realism, with no
inequality (no statistical Bell-type argument) involved. -/
