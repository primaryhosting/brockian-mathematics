/-
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-!
## Setting

We formalise the quantitative core of the fault-tolerance threshold theorem for
concatenated quantum error-correcting codes.

A fault-tolerance scheme is described by two constants:

* a *threshold constant* `c > 0`, coming from the combinatorics of the fault-tolerant
  gadget: a level-`(L+1)` gadget fails only if at least two of the level-`L` gadgets it is
  built from fail, which gives the error recursion `p_{L+1} = c * p_L ^ 2`;
* a *gadget size* `d`, the number of level-`L` gadgets used to build one level-`(L+1)`
  gadget, so that one logical operation at concatenation level `L` costs `d ^ L` physical
  operations.

Solving the recursion `p_0 = p`, `p_{L+1} = c * p_L ^ 2` gives the closed form
`p_L = (c * p) ^ (2 ^ L) / c`, which is taken as the definition below and shown to satisfy
the recursion.

The threshold is `p_th = 1 / c`: for any physical error rate `p < p_th` the logical error
rate `p_L` tends to `0` doubly exponentially fast in the number of levels, so an arbitrary
target accuracy `ε` is reached at some finite level, and the physical overhead `d ^ L`
needed is only polylogarithmic in `1 / ε`.
-/

/-- The logical error rate after `L` levels of code concatenation, for a fault-tolerance
scheme with threshold constant `c` and physical error rate `p`.  This is the solution of
the error recursion `p_0 = p`, `p_{L+1} = c * p_L ^ 2`. -/

noncomputable def errorAtLevel (c p : ℝ) (L : ℕ) : ℝ := (c * p) ^ (2 ^ L) / c

/-- At level `0` the logical error rate is the physical error rate. -/
