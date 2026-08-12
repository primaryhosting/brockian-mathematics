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
def DiffeoEquiv (A B : Smooth7Sphere) : Prop :=
  Nonempty (Diffeomorph I7 I7 A.carrier B.carrier ⊤)

/-- Diffeomorphism equivalence is reflexive. -/
theorem DiffeoEquiv.refl (A : Smooth7Sphere) : DiffeoEquiv A A :=
  ⟨Diffeomorph.refl I7 A.carrier ⊤⟩

/-- Diffeomorphism equivalence is symmetric. -/
theorem DiffeoEquiv.symm {A B : Smooth7Sphere} (h : DiffeoEquiv A B) : DiffeoEquiv B A :=
  h.elim fun f => ⟨f.symm⟩

/-- Diffeomorphism equivalence is transitive. -/
theorem DiffeoEquiv.trans {A B C : Smooth7Sphere} (h : DiffeoEquiv A B) (h' : DiffeoEquiv B C) :
    DiffeoEquiv A C :=
  h.elim fun f => h'.elim fun g => ⟨f.trans g⟩

/-- Diffeomorphic manifolds are in particular homeomorphic. -/
theorem DiffeoEquiv.toHomeomorph {A B : Smooth7Sphere} (h : DiffeoEquiv A B) :
    Nonempty (A.carrier ≃ₜ B.carrier) :=
  h.elim fun f => ⟨f.toHomeomorph⟩

/-- The round `7`-sphere with its standard smooth structure, viewed as a smooth homotopy
`7`-sphere. -/
noncomputable def standardSphere7 : Smooth7Sphere where
  carrier := S7
  homeomorphic := ⟨Homeomorph.refl S7⟩

@[simp] theorem standardSphere7_carrier : standardSphere7.carrier = S7 := rfl

/-!
## Exoticity

An *exotic* `7`-sphere is a smooth homotopy `7`-sphere which is not diffeomorphic to the standard
one. Unwinding the definitions, an exotic sphere is exactly a smooth manifold that is homeomorphic
but not diffeomorphic to `S⁷`.
-/

/-- `M` is an *exotic 7-sphere*: it is a smooth `7`-manifold homeomorphic to `S⁷`, but it is not
diffeomorphic to `S⁷`. -/
def IsExotic7Sphere (M : Smooth7Sphere) : Prop :=
  ¬ DiffeoEquiv M standardSphere7

/-- Unfolding: an exotic `7`-sphere really is a smooth manifold that is homeomorphic to `S⁷` and
admits no diffeomorphism onto `S⁷`. -/
theorem isExotic7Sphere_iff (M : Smooth7Sphere) :
    IsExotic7Sphere M ↔
      (Nonempty (M.carrier ≃ₜ S7) ∧ IsEmpty (Diffeomorph I7 I7 M.carrier S7 ⊤)) := by
  constructor
  · intro h
    exact ⟨M.homeomorphic, not_nonempty_iff.mp h⟩
  · rintro ⟨-, h⟩
    exact not_nonempty_iff.mpr h

/-!
## The invariant-theoretic reduction

Milnor's argument does not produce a diffeomorphism obstruction by hand: it produces a
*numerical invariant* of smooth homotopy `7`-spheres, the residue class

  `λ(M) = (d² - 1)  (mod 7)`

attached to the `S³`-bundle `M_{h,l}` over `S⁴` with `h + l = 1` and `d = h - l`.  It is a
diffeomorphism invariant, it vanishes on the standard sphere, and it is nonzero for suitable `d`.

The following section isolates that logical skeleton and checks it in Lean.
-/

/-- Milnor's residue invariant, as a function of the integer parameter `d = h - l` of the
bundle `M_{h,l}` over `S⁴` with `h + l = 1`.  Milnor's computation of the first Pontryagin class
and the signature defect gives `λ(M_{h,l}) = d² - 1 (mod 7)`. -/
def milnorLambda (d : ℤ) : ZMod 7 := ((d : ZMod 7)) ^ 2 - 1

/-- The invariant vanishes for the parameter value `d = 1`, which corresponds to the standard
sphere `M_{1,0} = S⁷`. -/
theorem milnorLambda_one : milnorLambda 1 = 0 := by
  simp [milnorLambda]

/-- **Base case of Milnor's computation.**  For `d = 3` the invariant is nonzero:
`3² - 1 = 8 ≡ 1 ≢ 0 (mod 7)`. -/
theorem milnorLambda_three_ne_zero : milnorLambda 3 ≠ 0 := by
  decide

/-- The invariant is nonzero for the parameter `d` exactly when `d² ≢ 1 (mod 7)`. -/
theorem milnorLambda_ne_zero_iff (d : ℤ) : milnorLambda d ≠ 0 ↔ ¬ ((d : ZMod 7)) ^ 2 = 1 := by
  simp [milnorLambda, sub_eq_zero]

/-- Odd parameters with a nonzero Milnor invariant exist in every residue class pattern:
concretely, `d = 3, 5, 9, 11, …`.  We record that there are infinitely many of them. -/
theorem exists_odd_milnorLambda_ne_zero (N : ℤ) :
    ∃ d : ℤ, N < d ∧ Odd d ∧ milnorLambda d ≠ 0 := by
  set k : ℤ := max N 0 with hk
  have hk0 : (0 : ℤ) ≤ k := le_max_right _ _
  have hkN : N ≤ k := le_max_left _ _
  refine ⟨14 * k + 17, by linarith, ⟨7 * k + 8, by ring⟩, ?_⟩
  have hcast : ((14 * k + 17 : ℤ) : ZMod 7) = 3 := by
    have h14 : (14 : ZMod 7) = 0 := by decide
    have h17 : (17 : ZMod 7) = 3 := by decide
    push_cast
    linear_combination (k : ZMod 7) * h14 + h17
  rw [milnorLambda, hcast]
  decide

/-!
### The reduction lemma

If some `ZMod 7`-valued function on smooth homotopy `7`-spheres is a diffeomorphism invariant and
separates `M` from the standard sphere, then `M` is exotic.  This is the exact logical step by
which Milnor's computation yields the existence of exotic spheres.
-/

/-- **Reduction.** A diffeomorphism-invariant function that separates `M` from the standard sphere
certifies that `M` is exotic. -/
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
theorem milnor_exotic_7sphere
    (lam : Smooth7Sphere → ZMod 7)
    (hinv : ∀ A B : Smooth7Sphere, DiffeoEquiv A B → lam A = lam B)
    (hstd : lam standardSphere7 = 0)
    (fam : ℤ → Smooth7Sphere)
    (hfam : ∀ d : ℤ, Odd d → lam (fam d) = milnorLambda d) :
    ∃ M : Smooth7Sphere,
      Nonempty (M.carrier ≃ₜ S7) ∧ IsEmpty (Diffeomorph I7 I7 M.carrier S7 ⊤) := by
  have h3 : lam (fam 3) ≠ lam standardSphere7 := by
    rw [hfam 3 ⟨1, by norm_num⟩, hstd]
    exact milnorLambda_three_ne_zero
  have hex : IsExotic7Sphere (fam 3) :=
    isExotic7Sphere_of_invariant_ne lam hinv (fam 3) h3
  exact ⟨fam 3, (isExotic7Sphere_iff _).mp hex⟩

end Frontier

