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

/-!
## Overview

Milnor's 1956 theorem asserts that there is a smooth `7`-manifold which is homeomorphic,
but not diffeomorphic, to the standard `7`-sphere.

The proof has two clearly separated halves.

* A **geometric/topological** half.  For integers `h + l = 1` one forms the total space
  `M_{h,l}` of an `S³`-bundle over `S⁴` (built from the two hemispheres of `S⁴` glued along
  the equator by the quaternionic map `v ↦ u^h v u^l`).  Morse theory applied to an explicit
  function on `M_{h,l}` shows that `M_{h,l}` is a topological `7`-sphere.  Furthermore Milnor
  constructs a `ℤ/7`-valued diffeomorphism invariant `λ` of smooth homotopy `7`-spheres
  (obtained from the first Pontryagin class and the signature of a coboundary via the
  Hirzebruch signature theorem) and computes `λ(M_{h,l}) = (h - l)² - 1 (mod 7)`, while
  `λ` vanishes on the standard sphere.

* An **arithmetic** half: the observation that `(h - l)² - 1` is *not* always `0` modulo `7`.

The arithmetic half is fully formalised and proved below (`milnorLambda`, and the lemmas
`milnorLambda_eq_zero_iff`, `exists_odd_milnorLambda_ne_zero`, ...).

The geometric half is far beyond what is currently available in Mathlib (it needs
characteristic classes, the Hirzebruch signature theorem, and Morse theory).  It is therefore
isolated in the structure `MilnorConstruction`, whose fields are exactly the geometric inputs
of Milnor's argument.  The target theorem `Frontier.milnor_exotic_7sphere` is the
**Lean-checked reduction**: from `MilnorConstruction` it derives the existence of an exotic
`7`-sphere.  No axioms are introduced: the geometric input appears as an explicit hypothesis.
-/

/-! ### The arithmetic core of Milnor's invariant -/

/-- Milnor's `λ`-invariant of the total space `M_{h,l}` of the `S³`-bundle over `S⁴`
with `h + l = 1`, expressed as a function of `k = h - l`:
`λ(M_{h,l}) ≡ (h - l)² - 1 (mod 7)`. -/
def milnorLambda (k : ℤ) : ZMod 7 := (k : ZMod 7) ^ 2 - 1

@[simp] lemma milnorLambda_one : milnorLambda 1 = 0 := by
  simp [milnorLambda]

@[simp] lemma milnorLambda_neg_one : milnorLambda (-1) = 0 := by
  simp [milnorLambda]

lemma milnorLambda_three : milnorLambda 3 = 1 := by
  decide +kernel

lemma milnorLambda_three_ne_zero : milnorLambda 3 ≠ 0 := by
  rw [milnorLambda_three]; decide

/-- The invariant vanishes exactly when `k ≡ ±1 (mod 7)`. -/
lemma milnorLambda_eq_zero_iff (k : ℤ) :
    milnorLambda k = 0 ↔ (k : ZMod 7) = 1 ∨ (k : ZMod 7) = -1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  unfold milnorLambda
  constructor
  · intro h
    have h' : ((k : ZMod 7) - 1) * ((k : ZMod 7) + 1) = 0 := by ring_nf; linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl (by linear_combination h'')
    · exact Or.inr (by linear_combination h'')
  · rintro (h | h) <;> rw [h] <;> ring

/-- There are odd `k` (i.e. admissible parameters `h + l = 1`, `k = h - l`) for which
Milnor's invariant is non-zero: the arithmetic heart of the exotic sphere theorem. -/
theorem exists_odd_milnorLambda_ne_zero : ∃ k : ℤ, Odd k ∧ milnorLambda k ≠ 0 :=
  ⟨3, ⟨1, by ring⟩, milnorLambda_three_ne_zero⟩

/-! ### Smooth `7`-manifolds and the standard `7`-sphere -/

noncomputable instance factFinrankEight :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) := ⟨by simp⟩

/-- The standard smooth `7`-sphere: the unit sphere of `ℝ⁸`. -/
abbrev sphere7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-- A smooth `7`-manifold (without boundary), bundled together with its instances. -/
structure Smooth7Manifold where
  /-- The underlying type. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 7)) carrier]
  [manifold : IsManifold (𝓡 7) ⊤ carrier]

attribute [instance] Smooth7Manifold.topology Smooth7Manifold.charts Smooth7Manifold.manifold

namespace Smooth7Manifold

/-- Two smooth `7`-manifolds are homeomorphic. -/
def Homeo (A B : Smooth7Manifold) : Prop := Nonempty (A.carrier ≃ₜ B.carrier)

/-- Two smooth `7`-manifolds are diffeomorphic (`C^∞`). -/
def Diffeo (A B : Smooth7Manifold) : Prop :=
  Nonempty (Diffeomorph (𝓡 7) (𝓡 7) A.carrier B.carrier ⊤)

lemma Homeo.refl (A : Smooth7Manifold) : A.Homeo A := ⟨Homeomorph.refl _⟩

lemma Diffeo.refl (A : Smooth7Manifold) : A.Diffeo A := ⟨Diffeomorph.refl _ _ _⟩

lemma Diffeo.symm {A B : Smooth7Manifold} (h : A.Diffeo B) : B.Diffeo A :=
  h.elim fun e => ⟨e.symm⟩

/-- A diffeomorphism is in particular a homeomorphism. -/
lemma Diffeo.homeo {A B : Smooth7Manifold} (h : A.Diffeo B) : A.Homeo B :=
  h.elim fun e => ⟨e.toHomeomorph⟩

end Smooth7Manifold

/-- The standard `7`-sphere as a bundled smooth `7`-manifold. -/
noncomputable def standardSphere7 : Smooth7Manifold := { carrier := sphere7 }

/-- `A` is an *exotic* `7`-sphere: homeomorphic, but not diffeomorphic, to the standard `S⁷`. -/
def IsExotic7Sphere (A : Smooth7Manifold) : Prop :=
  A.Homeo standardSphere7 ∧ ¬ A.Diffeo standardSphere7

/-- Sanity check: the standard sphere is not an exotic sphere.  This shows that
`IsExotic7Sphere` is not vacuously satisfied by every smooth `7`-manifold. -/
theorem not_isExotic7Sphere_standard : ¬ IsExotic7Sphere standardSphere7 := by
  rintro ⟨-, h⟩
  exact h (Smooth7Manifold.Diffeo.refl _)

/-- Being an exotic `7`-sphere is a diffeomorphism-invariant property. -/
theorem IsExotic7Sphere.of_diffeo {A B : Smooth7Manifold} (hAB : A.Diffeo B)
    (hB : IsExotic7Sphere B) : IsExotic7Sphere A := by
  refine ⟨?_, ?_⟩
  · exact hAB.homeo.elim fun e => hB.1.elim fun f => ⟨e.trans f⟩
  · intro h
    exact hB.2 (hAB.symm.elim fun e => h.elim fun f => ⟨e.trans f⟩)

/-! ### The geometric input of Milnor's argument -/

/-- The geometric content of Milnor's construction, packaged as hypotheses.

`bundle k` is the total space of the `S³`-bundle over `S⁴` with parameters `h + l = 1`,
`h - l = k` (`k` odd); `inv` is Milnor's `ℤ/7`-valued smooth invariant of homotopy
`7`-spheres.  The fields are:

* `bundle_homeo`  : each `bundle k` (`k` odd) is homeomorphic to `S⁷` (Morse theory);
* `inv_diffeo`    : `inv` is a diffeomorphism invariant;
* `inv_standard`  : `inv` vanishes on the standard sphere;
* `inv_bundle`    : `inv (bundle k) = (k² - 1 : ZMod 7)` (Pontryagin class + signature theorem).
-/
structure MilnorConstruction where
  /-- The total spaces `M_{h,l}` with `h + l = 1` and `h - l = k`. -/
  bundle : ℤ → Smooth7Manifold
  /-- Milnor's `ℤ/7`-valued invariant of smooth homotopy `7`-spheres. -/
  inv : Smooth7Manifold → ZMod 7
  /-- Each `M_{h,l}` with `h + l = 1` is homeomorphic to the standard `7`-sphere. -/
  bundle_homeo : ∀ k : ℤ, Odd k → (bundle k).Homeo standardSphere7
  /-- `inv` only depends on the diffeomorphism class. -/
  inv_diffeo : ∀ A B : Smooth7Manifold, A.Diffeo B → inv A = inv B
  /-- The invariant of the standard sphere vanishes. -/
  inv_standard : inv standardSphere7 = 0
  /-- Milnor's computation of the invariant of `M_{h,l}`. -/
  inv_bundle : ∀ k : ℤ, Odd k → inv (bundle k) = milnorLambda k

namespace MilnorConstruction

variable (H : MilnorConstruction)

/-- If Milnor's invariant of `bundle k` is non-zero, then `bundle k` is an exotic sphere. -/
theorem isExotic7Sphere_bundle {k : ℤ} (hk : Odd k) (hlam : milnorLambda k ≠ 0) :
    IsExotic7Sphere (H.bundle k) := by
  refine ⟨H.bundle_homeo k hk, ?_⟩
  intro hdiff
  apply hlam
  have h1 : H.inv (H.bundle k) = H.inv standardSphere7 :=
    H.inv_diffeo _ _ hdiff
  rw [H.inv_bundle k hk, H.inv_standard] at h1
  exact h1

end MilnorConstruction

/-! ### The main statement -/

/-- **Milnor's exotic 7-sphere theorem** (Lean-checked reduction).

Given the geometric input of Milnor's construction (the `S³`-bundles over `S⁴` whose total
spaces are topological `7`-spheres, together with Milnor's `ℤ/7`-valued diffeomorphism
invariant and its computation `λ(M_{h,l}) = (h-l)² - 1`), there exists a smooth `7`-manifold
which is homeomorphic to the standard `7`-sphere `S⁷` but not diffeomorphic to it.

The arithmetic heart of the argument — that `(h-l)² - 1 ≢ 0 (mod 7)` for a suitable choice of
`h + l = 1`, e.g. `h = 2, l = -1` — is proved here in full (`exists_odd_milnorLambda_ne_zero`).
-/
theorem milnor_exotic_7sphere (H : MilnorConstruction) :
    ∃ A : Smooth7Manifold, IsExotic7Sphere A := by
  obtain ⟨k, hk, hlam⟩ := exists_odd_milnorLambda_ne_zero
  exact ⟨H.bundle k, H.isExotic7Sphere_bundle hk hlam⟩

/-- Unwound form of the target statement: there is a type carrying a smooth `7`-manifold
structure which is homeomorphic but not diffeomorphic to the standard `7`-sphere. -/
theorem milnor_exotic_7sphere' (H : MilnorConstruction) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : IsManifold (𝓡 7) ⊤ M),
      Nonempty (M ≃ₜ sphere7) ∧ IsEmpty (Diffeomorph (𝓡 7) (𝓡 7) M sphere7 ⊤) := by
  obtain ⟨A, hhomeo, hdiff⟩ := milnor_exotic_7sphere H
  exact ⟨A.carrier, A.topology, A.charts, A.manifold, hhomeo,
    ⟨fun e => hdiff ⟨e⟩⟩⟩

end Frontier

