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

theorem hardy_quantum_fraction : bornProb hardyState uTwo vTwo = 1 / 12 := by
  have h : amp hardyState uTwo vTwo = -1 := by
    rw [expand]
    simp [hardyState, uTwo, vTwo]
    norm_num
  have hs : snorm hardyState = 3 := by
    simp [snorm, hardyState, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  have hu : qnorm uTwo = 2 := by
    simp [qnorm, uTwo, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  have hv : qnorm vTwo = 2 := by
    simp [qnorm, vTwo, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  rw [bornProb, h, hs, hu, hv]
  norm_num

/-!
## Part 3: the paradox
-/

/-- **Hardy's paradox.**

Quantum mechanics predicts, for the Hardy state `|00⟩ + |01⟩ + |10⟩` and the
indicated local measurement directions, that

* the three Hardy events `(a₁ = 1, b₂ = 1)`, `(a₂ = 1, b₁ = 1)`, `(a₁ = 0, b₁ = 0)`
  never occur, while
* the Hardy event `(a₂ = 1, b₂ = 1)` occurs in a fraction `1/12 > 0` of the runs.

No local deterministic hidden-variable model can reproduce these four numbers:
the three vanishing probabilities force the fourth to vanish as well.  Thus a
positive fraction of the runs — those in the Hardy event — witnesses the
failure of local realism directly, with no inequality involved. -/
