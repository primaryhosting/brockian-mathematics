import Mathlib

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

We work with the standard smooth model for `7`-dimensional manifolds: the model space is
`EuclideanSpace ℝ (Fin 7)` with the trivial `ModelWithCorners`, and the reference object is the
round `7`-sphere `S⁷ ⊆ EuclideanSpace ℝ (Fin 8)`, which Mathlib already equips with a smooth
manifold structure.
-/

/-- The model vector space for smooth `7`-manifolds. -/
abbrev E7 : Type := EuclideanSpace ℝ (Fin 7)

/-- The (corner-free) model with corners used for smooth `7`-manifolds. -/
noncomputable abbrev I7 : ModelWithCorners ℝ E7 E7 := modelWithCornersSelf ℝ E7

/-- The round `7`-sphere, sitting inside `ℝ⁸`. -/
abbrev S7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-!
## Homotopy 7-spheres

A *smooth homotopy `7`-sphere* (in the sense relevant to Milnor's theorem) is a smooth
`7`-manifold that is homeomorphic to the round sphere `S⁷`. We bundle the data.
-/

/-- A smooth `7`-manifold together with a homeomorphism to the round `7`-sphere `S⁷`.

This is the class of objects among which Milnor found manifolds that are *homeomorphic* but not
*diffeomorphic* to `S⁷`. -/
structure Smooth7Sphere : Type 1 where
  /-- The underlying set of points. -/
  carrier : Type
  /-- Its topology. -/
  [topology : TopologicalSpace carrier]
  /-- Its atlas of charts modelled on `ℝ⁷`. -/
  [charts : ChartedSpace E7 carrier]
  /-- The atlas is smooth (`C^∞`), so `carrier` is a smooth `7`-manifold. -/
  [smooth : IsManifold I7 ⊤ carrier]
  /-- The underlying topological space is homeomorphic to the round sphere `S⁷`. -/
  homeomorphic : Nonempty (carrier ≃ₜ S7)

attribute [instance] Smooth7Sphere.topology Smooth7Sphere.charts Smooth7Sphere.smooth

/-- Two smooth homotopy `7`-spheres are *equivalent* when they are diffeomorphic as smooth
manifolds. -/

theorem isExotic7Sphere_of_invariant_ne {Λ : Type} (lam : Smooth7Sphere → Λ)
    (hinv : ∀ A B : Smooth7Sphere, DiffeoEquiv A B → lam A = lam B)
    (M : Smooth7Sphere) (hM : lam M ≠ lam standardSphere7) :
    IsExotic7Sphere M := fun h => hM (hinv M standardSphere7 h)

/-!
## Main theorem
-/

/-- **Milnor's exotic 7-spheres (Lean-checked reduction, with the arithmetic base case).**

Assume the geometric input of Milnor's 1956 paper, stated as hypotheses:

* `lam` is a `ℤ/7`-valued invariant of smooth homotopy `7`-spheres, i.e. a function that is
  constant on diffeomorphism classes (`hinv`);
* it vanishes on the standard smooth `7`-sphere (`hstd`);
* Milnor's family of `S³`-bundles over `S⁴`: for each odd integer `d` there is a smooth
  homotopy `7`-sphere `fam d` (total space of the bundle `M_{h,l}` with `h + l = 1`, `h - l = d`)
  whose invariant is `milnorLambda d = d² - 1 (mod 7)` (`hfam`).

Then there exists a smooth manifold which is **homeomorphic but not diffeomorphic** to `S⁷`.

The proof supplies the arithmetic base case `d = 3`: `3² - 1 = 8 ≡ 1 ≢ 0 (mod 7)`, so `fam 3`
is separated from the standard sphere by `lam` and hence is exotic. -/
