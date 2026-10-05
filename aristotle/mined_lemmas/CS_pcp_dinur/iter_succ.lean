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

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- `iter f t g` is the `t`-fold iterate `f^[t] g`. -/

@[simp] theorem iter_succ {G : Type u} (f : G → G) (t : Nat) (g : G) :
    iter f (t + 1) g = f (iter f t g) := rfl

/-- For every `m ≥ 1` there is a power of two in the interval `[m, 2 * m)`;
this is what makes the number of amplification rounds logarithmic. -/
