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

/-- An abstract *fixed-kernel, pointwise-discard, linear* certificate.

`R` is the fixed kernel (the analytic object whose nonnegativity the certificate silently
assumes when it discards terms pointwise), and `weight` is the per-species linear charge. -/
structure Certificate (ι : Type*) where
  /-- The fixed kernel of the certificate. -/
  R : ℝ → ℝ
  /-- The per-species linear charge weights. -/
  weight : ι → ℝ
  /-- The charging is nonnegative (weights are a charge, not a signed measure). -/
  weight_nonneg : ∀ i : ι, 0 ≤ weight i

/-- Configuration data: each species is placed at a *deep point* of the kernel. -/
structure Configuration (ι : Type*) where
  /-- The deep point at which a given species sits. -/
  deepPoint : ι → ℝ

variable {ι : Type*}

/-- The linear functional the certificate evaluates on configuration data. -/

def IsDeepPairAt (cfg : Configuration ι) (z : ℝ) : Prop :=
  ∃ i j : ι, i ≠ j ∧ cfg.deepPoint i = z ∧ cfg.deepPoint j = z

/-- The certificate is *valid against deep-pair configurations* when its pointwise-discard
step is legitimate on every such configuration. -/
