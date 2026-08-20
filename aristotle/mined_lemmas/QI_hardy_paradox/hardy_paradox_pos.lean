import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace QI

/-- **Hardy's paradox, deterministic (local hidden variable) form.**

In a local realistic model, each hidden variable `l : Λ` deterministically fixes the outcomes
`a 1 l, a 2 l` of Alice's two possible measurement settings and `b 1 l, b 2 l` of Bob's.
The four Hardy conditions

* some run has `a₁ = b₁ = 1` (this is the positive-probability event),
* never `a₁ = 1` and `b₂ = 1`,
* never `a₂ = 1` and `b₁ = 1`,
* always `a₂ = 1` or `b₂ = 1`,

are jointly contradictory: no local hidden variable assignment can reproduce them. -/

theorem hardy_paradox_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Set Ω)
    (hpos : 0 < μ (A₁ ∩ B₁))
    (h₁ : μ (A₁ ∩ B₂) = 0)
    (h₂ : μ (A₂ ∩ B₁) = 0)
    (h₃ : μ (A₂ᶜ ∩ B₂ᶜ) = 0) :
    False :=
  absurd (hardy_paradox μ A₁ A₂ B₁ B₂ h₁ h₂ h₃) hpos.ne'

end QI

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

