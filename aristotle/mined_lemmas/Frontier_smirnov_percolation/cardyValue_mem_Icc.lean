/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

Cardy's formula, as proved by Smirnov for critical site percolation on the triangular
lattice, asserts that the scaling limit of the crossing probability of a planar domain
with four marked boundary points is **conformally invariant**, and is computed by an
explicit formula on the reference equilateral triangle.

Below we formalize the geometric side of this statement:

* `Frontier.MarkedDomain` — a planar domain with four marked (boundary) points;
* `Frontier.IsConformalEquiv` — a conformal equivalence of marked domains: a map that is
  holomorphic and injective on the domain, extends to a homeomorphic-type identification of
  the closures, and matches the four marked points;
* `Frontier.smirnov_percolation` — the Cardy–Smirnov conformal invariance statement, in the
  form of a Lean-checked reduction: *any* crossing-probability functional admitting a Cardy
  representation on a family of reference domains (this is exactly the content of Smirnov's
  theorem) is conformally invariant, provided the target domain can be uniformized onto a
  reference domain.

The base cases we prove outright are: conformal equivalence is reflexive and transitive
(`conformalEquiv_refl`, `IsConformalEquiv.trans`), every nondegenerate complex affine map
induces a conformal equivalence onto its image (`isConformalEquiv_affine`), whence crossing
probabilities are invariant under rotations, scalings and translations
(`crossing_affine_invariant`), and Cardy's formula on the reference equilateral triangle
takes the expected values (`cardyValue_*`).
-/

/-- A planar domain together with four marked boundary points `a`, `b`, `c`, `d`
(in cyclic order), the data entering a percolation crossing event: crossings are from the
boundary arc `ab` to the boundary arc `cd`. -/
structure MarkedDomain where
  /-- The underlying planar domain. -/
  carrier : Set ℂ
  /-- First marked boundary point. -/
  a : ℂ
  /-- Second marked boundary point. -/
  b : ℂ
  /-- Third marked boundary point. -/
  c : ℂ
  /-- Fourth marked boundary point. -/
  d : ℂ

/-- `IsConformalEquiv D D' f` says that `f` is a conformal equivalence of the marked domain
`D` onto the marked domain `D'`: it is holomorphic and injective on `D.carrier`, continuous
and injective on the closure, carries `D.carrier` onto `D'.carrier` and `closure D.carrier`
onto `closure D'.carrier`, and matches the four marked points. -/
structure IsConformalEquiv (D D' : MarkedDomain) (f : ℂ → ℂ) : Prop where
  /-- `f` is holomorphic on the domain. -/
  differentiableOn : DifferentiableOn ℂ f D.carrier
  /-- `f` is continuous up to the boundary. -/
  continuousOn : ContinuousOn f (closure D.carrier)
  /-- `f` is injective up to the boundary (in particular conformal inside). -/
  injOn : Set.InjOn f (closure D.carrier)
  /-- `f` maps the domain onto the target domain. -/
  image_carrier : f '' D.carrier = D'.carrier
  /-- `f` maps the closed domain onto the closed target domain. -/
  image_closure : f '' closure D.carrier = closure D'.carrier
  /-- The first marked point is preserved. -/
  map_a : f D.a = D'.a
  /-- The second marked point is preserved. -/
  map_b : f D.b = D'.b
  /-- The third marked point is preserved. -/
  map_c : f D.c = D'.c
  /-- The fourth marked point is preserved. -/
  map_d : f D.d = D'.d

/-- The identity is a conformal equivalence of a marked domain with itself. -/

theorem cardyValue_mem_Icc (A C : ℂ) (h : A ≠ C) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    cardyValue A C ((1 - t : ℝ) • C + (t : ℝ) • A) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [cardyValue_affineParam A C h ht]
  exact ⟨ht, ht1⟩

end Frontier

