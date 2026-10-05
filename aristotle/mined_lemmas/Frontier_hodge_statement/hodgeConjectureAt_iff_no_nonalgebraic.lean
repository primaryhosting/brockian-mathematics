import Mathlib
/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
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

set_option grind.warning false

namespace Frontier

open TensorProduct

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a rational vector
space `V` (conjugation on the left factor, identity on `V`).  It is only `ℚ`-linear
(it is conjugate-linear over `ℂ`). -/

theorem hodgeConjectureAt_iff_no_nonalgebraic (X : HodgeVariety H) (p : ℕ) :
    HodgeConjectureAt X p ↔ ¬ ∃ v : H p, v ∈ hodgeClasses X p ∧ v ∉ X.alg p := by
  constructor
  · rintro h ⟨v, hv, hv'⟩
    exact hv' (h ▸ hv)
  · intro h
    refine le_antisymm (alg_le_hodgeClasses X p) fun v hv => ?_
    by_contra hv'
    exact h ⟨v, hv, hv'⟩

/-- Equivalent "surjectivity" form of the whole conjecture. -/
