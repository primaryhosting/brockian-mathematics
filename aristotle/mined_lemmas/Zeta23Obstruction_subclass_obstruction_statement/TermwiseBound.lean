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

/-- A *deep-pair configuration*: two distinct "deep points" carrying strictly positive
species weights.  This is the abstract finite-dimensional model of the configuration data
a fixed-kernel certificate is tested against. -/
structure DeepPairConfig where
  /-- The (strictly positive) per-species weights. -/
  weight : Fin 2 → ℝ
  /-- The deep points at which the fixed kernel is evaluated. -/
  deep : Fin 2 → ℝ
  weight_pos : ∀ i, 0 < weight i
  deep_distinct : deep 0 ≠ deep 1

/-- The *pointwise discard* step of the certificate chain: each species' contribution is
discarded separately, so the chain's bound requires each term `weight i * R (deep i)` to be
nonnegative. -/

def TermwiseBound (R : ℝ → ℝ) (c : DeepPairConfig) : Prop :=
  ∀ i : Fin 2, 0 ≤ c.weight i * R (c.deep i)

/-- The linear charge functional attached to a configuration by a fixed kernel `R`. -/
