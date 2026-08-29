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

section Aumann

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {κ : Type*} [DecidableEq κ]

/-- The prior probability of an event `S ⊆ Ω`, for a weight function `p : Ω → ℝ`. -/

def IsClosed (part : Ω → κ) (C : Finset Ω) : Prop := ∀ ω ∈ C, cell part ω ⊆ C

/-- **Key lemma.**  If an event `C` is a union of an agent's information cells (i.e. it is
closed for that agent), and the agent's posterior probability of `E` equals `q` on every
cell meeting `C`, then the prior probability of `E ∩ C` is `q * prob C`: averaging the
constant posterior over the cells of `C` recovers the prior conditional probability. -/
