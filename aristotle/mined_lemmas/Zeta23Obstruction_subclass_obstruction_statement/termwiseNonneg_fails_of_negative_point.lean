/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

namespace Zeta23Obstruction

/-- A **configuration** of deep points: finitely many species, each carrying a real
"deep point" `pt i` and a strictly positive weight `wt i`. -/
structure DeepConfig where
  /-- number of species -/
  n : ℕ
  /-- the deep point attached to each species -/
  pt : Fin n → ℝ
  /-- the (strictly positive) weight attached to each species -/
  wt : Fin n → ℝ
  /-- positivity of the weights -/
  wt_pos : ∀ i : Fin n, 0 < wt i

/-- The **linear charge** of a configuration relative to a fixed kernel `R`:
the linear functional `c ↦ ∑ᵢ wᵢ · R(zᵢ)` obtained by per-species linear charging. -/

theorem termwiseNonneg_fails_of_negative_point (R : ℝ → ℝ) (c : DeepConfig) (i : Fin c.n)
    (hz : R (c.pt i) < 0) : ¬ TermwiseNonneg R c := by
  intro h
  have hw := c.wt_pos i
  have hi := h i
  nlinarith

/-- Validity of a fixed-kernel pointwise-discard certificate against *all* configurations,
not only deep pairs. -/
