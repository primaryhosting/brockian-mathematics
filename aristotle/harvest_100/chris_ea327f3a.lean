import Mathlib

/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header comment above is placed immediately after `import Mathlib`.

open scoped Polynomial

namespace Math

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in
`C([a,b], ℝ)` equipped with the sup norm.

The key input is Mathlib's `polynomialFunctions_closure_eq_top`, which says that the
subalgebra of polynomial functions on `Set.Icc a b` has topological closure `⊤`;
here we restate that as density of the corresponding set of continuous maps. -/
theorem weierstrass_approx (a b : ℝ) :
    Dense {f : C(Set.Icc a b, ℝ) | ∃ p : ℝ[X], p.toContinuousMapOn (Set.Icc a b) = f} := by
  have hs :
      ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
          Set C(Set.Icc a b, ℝ))
        = {f : C(Set.Icc a b, ℝ) | ∃ p : ℝ[X], p.toContinuousMapOn (Set.Icc a b) = f} := by
    rw [polynomialFunctions_coe]; rfl
  rw [← hs, dense_iff_closure_eq]
  have hclosure :
      ((polynomialFunctions (Set.Icc a b)).topologicalClosure : Set C(Set.Icc a b, ℝ))
        = ((⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ)) := by
    rw [polynomialFunctions_closure_eq_top]
  simpa using hclosure

/-- Sup-norm form of the Weierstrass approximation theorem: every continuous function on
`[a,b]` is within any `ε > 0`, in sup norm, of a polynomial function. -/
theorem weierstrass_approx_sup_norm (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε :=
  exists_polynomial_near_continuousMap a b f ε hε

end Math

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

