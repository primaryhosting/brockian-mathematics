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

/-- A *configuration* of deep-pair data: finitely many species, indexed by `ι`, each
carrying a nonnegative weight and a "deep point" at which the fixed kernel is evaluated. -/
structure Configuration (ι : Type) where
  /-- The nonnegative weight (mass) attached to each species. -/
  weight : ι → ℝ
  /-- The deep point at which the fixed kernel is sampled for each species. -/
  deep : ι → ℝ
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i

/-- The linear charge functional attached to a fixed kernel `R`: the total charge of a
configuration is the `R`-weighted sum over species.  It is linear in the weight vector. -/

theorem charge_nonneg_of_termwiseBound {ι : Type} [Fintype ι] (R : ℝ → ℝ)
    (C : Configuration ι) (h : TermwiseBound R C) : 0 ≤ charge R C :=
  Finset.sum_nonneg fun i _ => h i

/-- **Fixed kernel + pointwise discard has no slack**: validity of the certificate is
*equivalent* to global nonnegativity of the kernel. -/
