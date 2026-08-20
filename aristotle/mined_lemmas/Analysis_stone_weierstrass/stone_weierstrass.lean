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

theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  refine top_unique fun f _ => ?_
  show f ∈ closure ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
    Set C(Set.Icc a b, ℝ))
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_forall_abs_sub_lt a b f (half_pos hε)
  refine ⟨p.toContinuousMapOn (Set.Icc a b), ⟨p, trivial, rfl⟩, ?_⟩
  have hle : dist f (p.toContinuousMapOn (Set.Icc a b)) ≤ ε / 2 :=
    (ContinuousMap.dist_le (by positivity)).mpr fun x => by
      rw [Real.dist_eq, abs_sub_comm]
      exact (hp x).le
  linarith [half_lt_self hε]

end Analysis

