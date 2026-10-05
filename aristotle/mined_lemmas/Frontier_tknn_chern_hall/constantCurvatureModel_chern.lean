import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The Brillouin torus, modelled as the fundamental domain `[0, 2π] × [0, 2π]` in `ℝ × ℝ`. -/

@[simp] lemma constantCurvatureModel_chern (n : ℤ) : (constantCurvatureModel n).chern = n := rfl

/--
**TKNN (Thouless–Kohmoto–Nightingale–den Nijs).**

For a two-dimensional band insulator with Berry curvature `B.berry` and Chern number
`B.chern`, the Hall conductance is exactly quantized:

* it equals the Chern number times the conductance quantum `e²/h`;
* in particular it is an integer multiple of `e²/h`;
* and it obeys the dichotomy: either the Chern number vanishes and the Hall conductance
  is zero, or the Chern number is nonzero and the Hall conductance has magnitude at
  least one conductance quantum.
-/
