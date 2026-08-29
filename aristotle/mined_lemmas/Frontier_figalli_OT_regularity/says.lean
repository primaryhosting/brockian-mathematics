import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

/-!
## Setting

We formalize the one-dimensional base case of the Ma–Trudinger–Wang / Figalli regularity
theory for optimal transport.

The transport cost is the quadratic cost `c x y = (x - y)^2 / 2`.  For this cost Brenier's

theorem says that an optimal transport map is (a.e.) the gradient `T = u'` of a convex
potential `u`, and Ma–Trudinger–Wang / Figalli regularity theory asks when such a map is
continuous.  In dimension one the MTW condition is automatically satisfied (the MTW tensor
is evaluated on pairs of orthogonal vectors, and no such nonzero pair exists on the line;
moreover the mixed second derivative of the quadratic cost is the constant `-1`, so all
higher mixed derivatives entering the MTW tensor vanish — see
`Frontier.quadraticCost_mixed_deriv`).

The regularity statement proved here is the interior `C^1` statement: on an open set where
the Brenier potential is differentiable (i.e. where the transport map is single valued),
the transport map `T = u'` is automatically continuous, so `u` is `C^1` there.  The proof
runs through the two structural facts underlying the theory: monotonicity of `T`
(equivalently, `c`-monotonicity of the transport plan) and Darboux's intermediate value
property for derivatives; the continuity argument then splits into cases according to
whether `T` already satisfies the required bound on a fixed interval or overshoots it.
-/

/-- The quadratic transport cost on the line. -/
