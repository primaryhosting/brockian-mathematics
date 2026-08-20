import Mathlib
/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including module
-- docstrings, so the required header comment is placed immediately after `import Mathlib`.

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

namespace Math

open Polynomial

/-- **The Weierstrass approximation theorem.**
The set of (restrictions to `[a,b]` of) real polynomial functions is dense in the space
`C([a,b], ℝ)` of continuous functions on `[a,b]`, whose topology is the sup-norm topology.

The key Mathlib input is `polynomialFunctions_closure_eq_top`, which states that the
topological closure of the subalgebra of polynomial functions on `Set.Icc a b` is `⊤`. -/

theorem weierstrass_approx_sup_norm (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε :=
  exists_polynomial_near_continuousMap a b f ε hε

end Math

#print axioms Math.weierstrass_approx
#print axioms Math.weierstrass_approx_sup_norm

