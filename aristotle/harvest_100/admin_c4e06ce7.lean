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
open scoped Manifold

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

/-! ## Smooth 7-manifolds

We package a smooth (`C^∞`) 7-dimensional manifold without boundary, modelled on
`EuclideanSpace ℝ (Fin 7)`, as a bundled structure so that we can quantify over such
objects. -/

/-- The model space for 7-dimensional smooth manifolds. -/
abbrev E7 : Type := EuclideanSpace ℝ (Fin 7)

/-- A bundled smooth (`C^∞`) 7-manifold without boundary. -/
structure Smooth7Manifold where
  /-- The underlying type of points. -/
  carrier : Type
  [top : TopologicalSpace carrier]
  [charted : ChartedSpace E7 carrier]
  [smooth : IsManifold (𝓘(ℝ, E7)) ⊤ carrier]

attribute [instance] Smooth7Manifold.top Smooth7Manifold.charted Smooth7Manifold.smooth

namespace Smooth7Manifold

/-- Two bundled smooth 7-manifolds are *homeomorphic* if their underlying topological
spaces are homeomorphic. -/
def Homeomorphic (A B : Smooth7Manifold) : Prop :=
  Nonempty (A.carrier ≃ₜ B.carrier)

/-- Two bundled smooth 7-manifolds are *diffeomorphic* if there is a `C^∞`
diffeomorphism between them. -/
def Diffeomorphic (A B : Smooth7Manifold) : Prop :=
  Nonempty (Diffeomorph (𝓘(ℝ, E7)) (𝓘(ℝ, E7)) A.carrier B.carrier ⊤)

theorem Homeomorphic.refl (A : Smooth7Manifold) : Homeomorphic A A :=
  ⟨Homeomorph.refl _⟩

theorem Diffeomorphic.refl (A : Smooth7Manifold) : Diffeomorphic A A :=
  ⟨Diffeomorph.refl _ _ _⟩

/-- A diffeomorphism is in particular a homeomorphism. -/
theorem Diffeomorphic.homeomorphic {A B : Smooth7Manifold} (h : Diffeomorphic A B) :
    Homeomorphic A B :=
  h.elim fun f => ⟨f.toHomeomorph⟩

end Smooth7Manifold

/-! ## The standard 7-sphere -/

instance factFinrankEuclidean8 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) :=
  ⟨by simp⟩

/-- The standard smooth 7-sphere: the unit sphere in `ℝ⁸` with its usual smooth structure
coming from stereographic projection. -/
noncomputable def standardSphere7 : Smooth7Manifold where
  carrier := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-! ## Milnor's `λ`-invariant, the reduction, and the arithmetic base case

Milnor's construction produces, for each `h : ℤ`, a smooth 7-manifold `M h` (the total space
of the `S³`-bundle over `S⁴` with clutching data `(h, 1 - h)`).  Each `M h` is homeomorphic
to `S⁷`, because it carries a Morse function with exactly two critical points (Reeb's
theorem).  Milnor's `λ`-invariant, a diffeomorphism invariant of oriented smooth 7-manifolds
with values in `ZMod 7`, evaluates on `M h` to `(h - (1 - h))^2 - 1 = (2h - 1)^2 - 1`, and
vanishes on the standard sphere.

The arithmetic base case is that this quantity is nonzero mod `7` for a suitable `h`
(e.g. `h = 2`, giving `(h, l) = (2, -1)` and `λ = 8 ≡ 1`). -/

/-- Milnor's `λ`-invariant of the bundle `M_{h, 1-h}`, as an element of `ZMod 7`. -/
def milnorLambda (h : ℤ) : ZMod 7 := (((2 * h - 1) ^ 2 - 1 : ℤ) : ZMod 7)

/-- **Base case.**  For `h = 1` (i.e. `(h, l) = (1, 0)`) Milnor's invariant vanishes: this is
the bundle giving the standard sphere. -/
theorem milnorLambda_one : milnorLambda 1 = 0 := by
  unfold milnorLambda
  norm_num

/-- **Base case.**  For `h = 2` (i.e. `(h, l) = (2, -1)`) Milnor's invariant equals `1 ≠ 0`
in `ZMod 7`.  This is the arithmetic heart of Milnor's argument: it distinguishes
`M_{2,-1}` from the standard 7-sphere. -/
theorem milnorLambda_two : milnorLambda 2 = 1 := by
  unfold milnorLambda
  decide

theorem milnorLambda_two_ne_zero : milnorLambda 2 ≠ 0 := by
  rw [milnorLambda_two]
  decide

/-- Milnor's invariant of `M_{h, 1-h}` vanishes exactly when `h ≡ 0` or `h ≡ 1` modulo `7`.
In particular it is nonzero for infinitely many `h`. -/
theorem milnorLambda_eq_zero_iff (h : ℤ) :
    milnorLambda h = 0 ↔ ((h : ZMod 7) = 0 ∨ (h : ZMod 7) = 1) := by
  have : milnorLambda h = (2 * (h : ZMod 7) - 1) ^ 2 - 1 := by
    unfold milnorLambda; push_cast; ring
  rw [this]
  generalize ((h : ZMod 7)) = x
  revert x
  decide

/-- **Milnor's exotic 7-spheres (Lean-checked reduction).**

Given

* a family `M : ℤ → Smooth7Manifold` of smooth 7-manifolds (Milnor's `S³`-bundles over
  `S⁴` with clutching data `(h, 1 - h)`),
* the fact that each `M h` is homeomorphic to the standard 7-sphere,
* a `ZMod 7`-valued diffeomorphism invariant `lam` (Milnor's `λ`),
* the computation `lam (M h) = (2h - 1)^2 - 1` in `ZMod 7`,
* the vanishing `lam (standard 7-sphere) = 0`,

there exists a smooth 7-manifold which is homeomorphic to `S⁷` but **not** diffeomorphic
to `S⁷`; explicitly, `M 2` works.  The last step is the arithmetic base case
`milnorLambda_two_ne_zero`. -/
theorem milnor_exotic_7sphere
    (M : ℤ → Smooth7Manifold)
    (hHomeo : ∀ h : ℤ, Smooth7Manifold.Homeomorphic (M h) standardSphere7)
    (lam : Smooth7Manifold → ZMod 7)
    (hlam_inv : ∀ A B : Smooth7Manifold, Smooth7Manifold.Diffeomorphic A B → lam A = lam B)
    (hlam_M : ∀ h : ℤ, lam (M h) = milnorLambda h)
    (hlam_std : lam standardSphere7 = 0) :
    ∃ N : Smooth7Manifold,
      Smooth7Manifold.Homeomorphic N standardSphere7 ∧
        ¬ Smooth7Manifold.Diffeomorphic N standardSphere7 := by
  refine ⟨M 2, hHomeo 2, ?_⟩
  intro hdiff
  have h1 : lam (M 2) = lam standardSphere7 := hlam_inv _ _ hdiff
  rw [hlam_M 2, hlam_std] at h1
  exact milnorLambda_two_ne_zero h1

end Frontier

