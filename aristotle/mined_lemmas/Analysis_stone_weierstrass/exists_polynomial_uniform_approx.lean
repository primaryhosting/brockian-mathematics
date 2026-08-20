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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

/-- Key intermediate lemma: the set of polynomial functions on a compact interval `[a,b]`
is dense in the space `C([a,b], ℝ)` of continuous functions with the uniform (sup) norm. -/

theorem exists_polynomial_uniform_approx (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |Polynomial.eval (x : ℝ) p - f x| < ε := by
  obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.1
    ((dense_polynomialFunctions a b) f) ε hε
  rw [SetLike.mem_coe, ← SetLike.mem_coe, polynomialFunctions_coe] at hg
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have hx : dist (f x) ((Polynomial.toContinuousMapOnAlgHom (Set.Icc a b) p) x) < ε :=
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) hgf
  rw [Real.dist_eq] at hx
  simpa [Polynomial.toContinuousMapOnAlgHom, Polynomial.toContinuousMapOn,
    Polynomial.toContinuousMap, abs_sub_comm] using hx

/-- **The Stone–Weierstrass theorem (polynomial / Weierstrass approximation form).**

On a compact interval `[a,b] ⊆ ℝ`, the subalgebra of polynomial functions is dense in
`C([a,b], ℝ)` for the uniform norm: its topological closure is the whole algebra.
Equivalently (second conjunct), every continuous function on `[a,b]` is a uniform limit
of polynomials. -/
