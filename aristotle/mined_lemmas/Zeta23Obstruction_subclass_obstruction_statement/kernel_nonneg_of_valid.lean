import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Obstruction

/-- An abstract *fixed-kernel pointwise-discard linear certificate*.

`ι` indexes the (finitely many) *species*.  The certificate is fixed once and for all:
it consists of a single kernel `R : ℝ → ℝ` (the analytic continuation of the certificate
kernel, in the concrete setting) together with strictly positive per-species charging
weights `w`.  The certificate charges a configuration linearly through `R`, and it
*discards* each term pointwise, so its validity requires each discarded term to be
nonnegative. -/
structure Certificate (ι : Type) where
  /-- The fixed kernel of the certificate. -/
  R : ℝ → ℝ
  /-- Per-species linear charging weights. -/
  w : ι → ℝ
  /-- The charging weights are strictly positive. -/
  hw : ∀ i, 0 < w i

variable {ι : Type}

/-- The linear charge assigned by the certificate to a configuration `z`, which records
the deep point attached to each species. -/

theorem kernel_nonneg_of_valid [Fintype ι] (hι : 2 ≤ Fintype.card ι) (C : Certificate ι)
    (hvalid : ∀ z : ι → ℝ, C.ValidAgainst z) : ∀ x, 0 ≤ C.R x := by
  intro x
  by_contra hx
  obtain ⟨z, -, hbad, -⟩ := subclass_obstruction_statement hι C x (not_le.mp hx)
  exact hbad (hvalid z)

end Zeta23Obstruction

import Mathlib

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

