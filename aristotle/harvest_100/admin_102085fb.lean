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

/-- **Stone–Weierstrass theorem, polynomial form.**
On a compact interval `[a, b] ⊆ ℝ`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of continuous real-valued functions with the uniform (sup) norm: its
topological closure is the whole space. -/
theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
  polynomialFunctions_closure_eq_top a b

/-- Uniform-approximation form of the Stone–Weierstrass theorem: every continuous function on
`[a, b]` is uniformly approximated to any prescribed accuracy `ε > 0` by a polynomial. -/
theorem stone_weierstrass_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  have hmem : f ∈ closure ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := by
    have hf : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
      rw [stone_weierstrass a b]; trivial
    exact hf
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  rw [polynomialFunctions_coe] at hg
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have hle := ContinuousMap.dist_apply_le_dist (f := f)
    (g := (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)) p) x
  simp only [Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_apply] at hle ⊢
  rw [abs_sub_comm]
  calc |f x - Polynomial.eval (x : ℝ) p| ≤ dist f _ := hle
    _ < ε := hdist

end Analysis

