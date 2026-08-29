/-
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the header above uses `/- -/` rather than `/-! -/` since a module docstring
-- may not precede the `import` command in Lean 4; its text is otherwise as specified.

import Mathlib

open Polynomial ContinuousMap

namespace Math

/-- **Weierstrass approximation theorem.**
The polynomial functions are dense in `C([a,b], ℝ)`, which carries the sup norm.

The proof is Mathlib's `polynomialFunctions_closure_eq_top`, which states that the
subalgebra of polynomial functions on `Set.Icc a b` has topological closure `⊤`;
here it is repackaged as density of the set of restrictions of polynomials. -/
theorem weierstrass_approx (a b : ℝ) :
    Dense (Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b)) := by
  have h := polynomialFunctions_closure_eq_top a b
  have hset : (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) =
      Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b) := by
    simp [polynomialFunctions, Polynomial.toContinuousMapOnAlgHom]
  rw [← hset, dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, h]
  simp

/-- Epsilon form of the Weierstrass approximation theorem: every continuous function on
`[a,b]` is within `ε` of a polynomial in the sup norm. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε := by
  obtain ⟨g, ⟨p, rfl⟩, hg⟩ :=
    (weierstrass_approx a b).exists_mem_open (Metric.isOpen_ball (x := f) (ε := ε)) ⟨f, by
      simpa using hε⟩
  exact ⟨p, by simpa [dist_eq_norm] using Metric.mem_ball.mp hg⟩

/-- Pointwise epsilon form: any function continuous on `[a,b]` is uniformly approximated
on `[a,b]` by a polynomial. -/
theorem weierstrass_approx_pointwise (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
  exists_polynomial_near_of_continuousOn a b f hf ε hε

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

