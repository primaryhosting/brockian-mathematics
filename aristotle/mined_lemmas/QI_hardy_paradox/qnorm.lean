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
## Part 1: local realism

A *local deterministic hidden-variable model* for a two-party, two-setting,
two-outcome experiment is a probability space `(Ω, μ)` (the hidden variable)
together with response functions `a₁ a₂ b₁ b₂ : Ω → Bool`: `aᵢ ω` is Alice's
outcome when she chooses setting `i` and the hidden variable is `ω` (and it does
not depend on Bob's setting), similarly for Bob.

Hardy's argument shows that the three "impossibility" constraints

* `a₁ = 1` and `b₂ = 1` never happens,
* `a₂ = 1` and `b₁ = 1` never happens,
* `a₁ = 0` and `b₁ = 0` never happens,

force the *Hardy event* `a₂ = 1 ∧ b₂ = 1` to have probability `0`.
No inequality is involved: a single run of the Hardy event already refutes the model.
-/

/-- The key combinatorial step of Hardy's argument: in any local deterministic
model, the Hardy event is contained in the union of the three forbidden events. -/

def qnorm (u : Fin 2 → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

/-- Squared norm of a (unnormalised) two-qubit state. -/
