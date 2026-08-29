/-
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede every command, including module doc comments `/-! -/`,
-- so the required header appears above as an ordinary block comment and is repeated as the
-- module docstring immediately after the imports.)

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

open MeasureTheory

namespace QI

/-!
## Part 1: the local-realistic (hidden-variable) side

A local hidden-variable model for a two-party, two-settings-per-party experiment is a
probability space `Ω` (the space of hidden variables / runs) together with four outcome
functions

* `A₁ A₂ : Ω → Bool` — Alice's outcome for her setting `1` resp. `2`,
* `B₁ B₂ : Ω → Bool` — Bob's outcome for his setting `1` resp. `2`.

Locality and realism are encoded structurally: each outcome is a function of the run `ω`
alone, and in particular Alice's outcome does not depend on Bob's setting and vice versa.
Hardy's argument shows that the four Hardy conditions are then contradictory — a
*logical* (inequality-free) obstruction, unlike CHSH.
-/

/-- The pointwise (run-by-run) core of Hardy's argument: any run in which Alice's second
outcome and Bob's second outcome are both `true` must lie in one of the three Hardy
"forbidden" events. -/

theorem hardy_prob_eq_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Ω → Bool)
    (h₁ : μ {ω | A₂ ω = true ∧ B₁ ω = false} = 0)
    (h₂ : μ {ω | A₁ ω = false ∧ B₂ ω = true} = 0)
    (h₃ : μ {ω | A₁ ω = true ∧ B₁ ω = true} = 0) :
    μ {ω | A₂ ω = true ∧ B₂ ω = true} = 0 := by
  by_contra h
  exact hardy_paradox μ A₁ A₂ B₁ B₂ h₁ h₂ h₃ (pos_iff_ne_zero.mpr h)

/-!
## Part 2: the quantum side — a positive fraction of runs

Quantum mechanics satisfies the three Hardy null conditions while giving the Hardy event
probability `1/12 > 0`; by Part 1 that fraction of runs has no local-realistic
explanation.

We work with an explicit two-qubit system, `Fin 2 → Fin 2 → ℂ` (amplitudes `ψ i j` in the
product basis).  Probabilities are given by the Born rule, written here in a
normalisation-free way: for a (nonzero) state `ψ` and local vectors `a`, `b`,
`bornProb ψ a b = |⟨a ⊗ b, ψ⟩|² / (‖ψ‖² ‖a‖² ‖b‖²)`, which is the usual Born probability
`|⟨a ⊗ b, ψ⟩|²` once `ψ`, `a`, `b` are unit vectors.
-/

/-- The amplitude `⟨a ⊗ b, ψ⟩` of the product vector `a ⊗ b` in the two-qubit state `ψ`. -/
