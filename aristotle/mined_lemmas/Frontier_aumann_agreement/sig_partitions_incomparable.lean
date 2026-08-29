/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset

variable {Ω ι κ : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The information cell (element of the information partition) of an agent whose
information is described by the signal function `f`, at the state `ω`:
the set of states the agent cannot distinguish from `ω`. -/

lemma sig_partitions_incomparable :
    sig₁ 0 = sig₁ 1 ∧ sig₂ 0 ≠ sig₂ 1 ∧ sig₂ 1 = sig₂ 2 ∧ sig₁ 1 ≠ sig₁ 2 := by
  decide

/-- All hypotheses of `aumann_agreement` are satisfiable: with the uniform prior on four
states, the event `E = {0, 2}`, the common knowledge event `M = univ`, and the two
different information partitions `sig₁`, `sig₂`, both agents' posteriors equal `1/2`
everywhere (and indeed the conclusion `q₁ = q₂` holds). -/
