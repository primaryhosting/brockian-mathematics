/-
# Stone Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.stone_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

/-- **Key intermediate lemma (uniform approximation by polynomials).**
Every continuous real-valued function on a compact interval `[a, b]` can be approximated,
uniformly on `[a, b]` and to any prescribed accuracy `ε > 0`, by a real polynomial. -/

theorem exists_polynomial_forall_abs_sub_lt (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ}
    (hε : 0 < ε) : ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |Polynomial.eval (x : ℝ) p - f x| < ε := by
  -- `f` lies in the topological closure of the polynomial functions, by Weierstrass approximation.
  have hf : f ∈ closure ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := continuousMap_mem_polynomialFunctions_closure a b f
  -- Extract an element of the subalgebra at distance `< ε` from `f`.
  obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨p, -, hp⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have hpx : Polynomial.eval (x : ℝ) p = g x := by rw [← hp]; rfl
  have hdist : dist (f x) (g x) ≤ dist f g := ContinuousMap.dist_apply_le_dist x
  rw [Real.dist_eq] at hdist
  rw [hpx, abs_sub_comm]
  exact lt_of_le_of_lt hdist hgf

/-- **The Stone–Weierstrass theorem (polynomial form).**
On a compact interval `[a, b]`, the subalgebra of polynomial functions is dense in the algebra
`C([a,b], ℝ)` of continuous real-valued functions with the uniform norm: its topological closure
is the whole space. -/
