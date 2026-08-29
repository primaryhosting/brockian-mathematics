import Mathlib

/-!
# Stone Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.stone_weierstrass
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

open scoped Polynomial

/-- **Stone–Weierstrass theorem, polynomial form.**

On a compact interval `[a, b]`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of continuous real-valued functions with the uniform norm:
its topological closure is the whole space. -/
theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
  polynomialFunctions_closure_eq_top a b

/-- Every continuous function on `[a, b]` lies in the closure of the polynomial functions. -/
theorem stone_weierstrass_mem_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [stone_weierstrass a b]
  exact Algebra.mem_top

/-- **Stone–Weierstrass, ε-form.** Every real-valued function that is continuous on `[a, b]`
can be uniformly approximated on `[a, b]` to within any `ε > 0` by a polynomial. -/
theorem stone_weierstrass_eps (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  -- Package `f` as a bundled continuous map on the compact interval.
  set f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  -- `f'` is in the closure of the polynomial functions, hence within `ε` of one of them.
  have w := Metric.mem_closure_iff.mp
    (by simpa [Subalgebra.topologicalClosure_coe] using
      (stone_weierstrass_mem_closure a b f' : f' ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure))
  obtain ⟨g, hg, hgd⟩ := w ε hε
  obtain ⟨p, -, rfl⟩ := hg
  refine ⟨p, fun x hx => ?_⟩
  have hlt : ‖Polynomial.toContinuousMapOn p (Set.Icc a b) - f'‖ < ε := by
    rw [← dist_eq_norm]; simpa [dist_comm] using hgd
  have := (ContinuousMap.norm_lt_iff _ hε).mp hlt ⟨x, hx⟩
  simpa [f', Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
    Real.norm_eq_abs] using this

end Analysis


