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

theorem certificate_sound_of_kernel_nonneg (R : ℝ → ℝ) (h_pos : ∀ x, 0 ≤ R x)
    (c : DeepPairConfig) : TermwiseBound R c ∧ 0 ≤ charge R c := by
  have hterm : TermwiseBound R c := fun i =>
    mul_nonneg (c.weight_pos i).le (h_pos _)
  refine ⟨hterm, ?_⟩
  exact Finset.sum_nonneg fun i _ => hterm i

/-- **Abstract subclass obstruction.**

For a certificate with *fixed kernel* `R : ℝ → ℝ`, used via *pointwise discard* and
per-species linear charging, the existence of a single point `z` with `R z < 0` (the
"bad deep value" of the repaired witness) is *equivalent* to the existence of a deep-pair
configuration on which both the termwise bound and the linear charge bound fail.

Thus: fixed kernel + pointwise discard + one bad deep value ⟹ the certificate is invalid
against deep-pair configurations. -/
