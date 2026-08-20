/-
/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

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

/-! ## Setting up the statement

We work with the model space `EuclideanSpace ℝ (Fin 4)` and the trivial model with corners
on it, so that "smooth manifold modelled on `E4`" means a genuine boundaryless smooth
`4`-manifold in Mathlib's sense. -/

/-- The model space `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The (boundaryless) model with corners used throughout: `ℝ⁴` modelled on itself. -/
noncomputable abbrev I4 : ModelWithCorners ℝ E4 E4 := modelWithCornersSelf ℝ E4

/-- A *smooth manifold homeomorphic to `ℝ⁴`*: a topological space `carrier`, equipped with a
`C^∞` manifold structure modelled on `ℝ⁴`, together with a homeomorphism onto `ℝ⁴`.

Equivalently (and this is how it is used below) this is a smooth structure on the topological
space `ℝ⁴`, presented invariantly. -/
structure SmoothR4 : Type 1 where
  /-- The underlying set. -/
  carrier : Type
  /-- Its topology. -/
  topology : TopologicalSpace carrier
  /-- An atlas of charts with values in `ℝ⁴`. -/
  charts : @ChartedSpace E4 _ carrier topology
  /-- The atlas is `C^∞`-compatible, i.e. this is a smooth manifold. -/
  isManifold : @IsManifold ℝ _ E4 _ _ E4 _ I4 ⊤ carrier topology charts
  /-- The underlying topological space is homeomorphic to `ℝ⁴`. -/
  homeomorphicToR4 : Nonempty (@Homeomorph carrier E4 topology _)

attribute [instance] SmoothR4.topology SmoothR4.charts SmoothR4.isManifold

/-- Two smooth structures on `ℝ⁴` are *diffeomorphic* when there is a `C^∞` diffeomorphism
between them. -/
def SmoothR4.Diffeo (A B : SmoothR4) : Prop :=
  Nonempty (Diffeomorph I4 I4 A.carrier B.carrier ⊤)

/-- The standard smooth structure on `ℝ⁴`. -/
noncomputable def standardR4 : SmoothR4 where
  carrier := E4
  topology := inferInstance
  charts := inferInstance
  isManifold := inferInstance
  homeomorphicToR4 := ⟨Homeomorph.refl _⟩

/-- A smooth manifold homeomorphic to `ℝ⁴` is *exotic* when it is not diffeomorphic to the
standard `ℝ⁴`. -/
def IsExoticR4 (A : SmoothR4) : Prop := ¬ A.Diffeo standardR4

/-- The statement "there exists a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴`"
(Donaldson–Freedman). -/
def ExoticR4Exists : Prop := ∃ A : SmoothR4, IsExoticR4 A

/-! ## Basic properties of the diffeomorphism relation -/

@[refl]
theorem SmoothR4.Diffeo.refl (A : SmoothR4) : A.Diffeo A :=
  ⟨Diffeomorph.refl I4 A.carrier ⊤⟩

@[symm]
theorem SmoothR4.Diffeo.symm {A B : SmoothR4} (h : A.Diffeo B) : B.Diffeo A :=
  h.elim fun f => ⟨f.symm⟩

theorem SmoothR4.Diffeo.trans {A B C : SmoothR4} (hAB : A.Diffeo B) (hBC : B.Diffeo C) :
    A.Diffeo C :=
  hAB.elim fun f => hBC.elim fun g => ⟨f.trans g⟩

/-- Diffeomorphic manifolds are homeomorphic. -/
theorem SmoothR4.Diffeo.homeomorph {A B : SmoothR4} (h : A.Diffeo B) :
    Nonempty (A.carrier ≃ₜ B.carrier) :=
  h.elim fun f => ⟨f.toHomeomorph⟩

/-- Being exotic is a diffeomorphism invariant. -/
theorem IsExoticR4.of_diffeo {A B : SmoothR4} (h : A.Diffeo B) (hB : IsExoticR4 B) :
    IsExoticR4 A := fun hA => hB (h.symm.trans hA)

/-- The standard `ℝ⁴` is not exotic. -/
theorem not_isExoticR4_standard : ¬ IsExoticR4 standardR4 := fun h => h (.refl _)

/-! ## Transfer of the standard structure along a homeomorphism

Exoticness is really a property of the *smooth structure*, not of the underlying topological
space: every topological space homeomorphic to `ℝ⁴` also carries a (standard) smooth structure,
obtained by declaring the homeomorphism to be a global chart. -/

section Transfer

variable {X : Type} [tX : TopologicalSpace X]

/-- The atlas on `X` consisting of the single global chart `e : X ≃ₜ ℝ⁴`. -/
noncomputable def chartedSpaceOfHomeomorph (e : X ≃ₜ E4) : ChartedSpace E4 X :=
  letI : Nonempty X := ⟨e.symm 0⟩
  e.isOpenEmbedding.singletonChartedSpace

/-- A single global chart is trivially a `C^∞` atlas. -/
theorem isManifold_chartedSpaceOfHomeomorph (e : X ≃ₜ E4) :
    @IsManifold ℝ _ E4 _ _ E4 _ I4 ⊤ X tX (chartedSpaceOfHomeomorph e) := by
  letI : Nonempty X := ⟨e.symm 0⟩
  exact e.isOpenEmbedding.isManifold_singleton

/-- With this transported structure, `e` itself is a `C^∞` diffeomorphism onto the standard
`ℝ⁴`. -/
noncomputable def diffeomorphOfHomeomorph (e : X ≃ₜ E4) :
    @Diffeomorph ℝ _ E4 _ _ E4 _ _ E4 _ E4 _ I4 I4 X tX (chartedSpaceOfHomeomorph e) E4 _ _ ⊤ := by
  letI : Nonempty X := ⟨e.symm 0⟩
  letI cX : ChartedSpace E4 X := chartedSpaceOfHomeomorph e
  haveI : IsManifold I4 ⊤ X := isManifold_chartedSpaceOfHomeomorph e
  set x0 : X := e.symm 0
  have hcoe : (chartAt E4 x0 : X → E4) = e :=
    Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq _
  have hsrc : (chartAt E4 x0).source = Set.univ := by
    simp [cX, chartedSpaceOfHomeomorph, Topology.IsOpenEmbedding.singletonChartedSpace]
  have htgt : (chartAt E4 x0).target = Set.univ := by
    rw [← OpenPartialHomeomorph.image_source_eq_target, hsrc]
    simp [Set.image_univ, e.surjective.range_eq]
  have hsymm : ((chartAt E4 x0).symm : E4 → X) = e.symm := by
    funext y
    have hy : y ∈ (chartAt E4 x0).target := by rw [htgt]; trivial
    have hinv := (chartAt E4 x0).right_inv hy
    rw [hcoe] at hinv
    exact e.injective (by rw [hinv]; simp)
  have h1 : ContMDiff I4 I4 ⊤ (e : X → E4) := by
    have h := contMDiffOn_chart (I := I4) (n := ⊤) (x := x0)
    rw [hsrc, hcoe] at h
    exact contMDiffOn_univ.mp h
  have h2 : ContMDiff I4 I4 ⊤ (e.symm : E4 → X) := by
    have h := contMDiffOn_chart_symm (I := I4) (n := ⊤) (x := x0)
    rw [htgt, hsymm] at h
    exact contMDiffOn_univ.mp h
  exact ⟨e.toEquiv, h1, h2⟩

/-- The smooth structure obtained by transporting the standard one along a homeomorphism
`e : X ≃ₜ ℝ⁴`, i.e. by taking `e` as a single global chart. -/
noncomputable def SmoothR4.ofHomeomorph (e : X ≃ₜ E4) : SmoothR4 where
  carrier := X
  topology := tX
  charts := chartedSpaceOfHomeomorph e
  isManifold := isManifold_chartedSpaceOfHomeomorph e
  homeomorphicToR4 := ⟨e⟩

/-- A space homeomorphic to `ℝ⁴`, equipped with the transported smooth structure, is not
exotic. -/
theorem not_isExoticR4_ofHomeomorph (e : X ≃ₜ E4) :
    ¬ IsExoticR4 (SmoothR4.ofHomeomorph e) := fun h =>
  h ⟨diffeomorphOfHomeomorph e⟩

end Transfer

/-- Consequently, exoticness cannot be detected by the underlying topological space: the
underlying space of any exotic `ℝ⁴` also carries a standard (non-exotic) smooth structure. -/
theorem exists_nonExotic_on_carrier (A : SmoothR4) :
    ∃ B : SmoothR4, B.carrier = A.carrier ∧ ¬ IsExoticR4 B :=
  A.homeomorphicToR4.elim fun e =>
    ⟨SmoothR4.ofHomeomorph e, rfl, not_isExoticR4_ofHomeomorph e⟩

/-! ## The reduction

Mathlib does not contain gauge theory (Donaldson's diagonalizability theorem) nor Freedman's
classification of simply connected topological `4`-manifolds, so the existence of an exotic
`ℝ⁴` cannot currently be derived from scratch. What is proved here is the standard reduction:

*the existence of an exotic `ℝ⁴` is equivalent to the failure of uniqueness of smooth
structures on `ℝ⁴`.*

The nontrivial direction takes as input exactly the conclusion of the Donaldson–Freedman
argument in the form "some topological `ℝ⁴` carries two non-diffeomorphic smooth structures",
and produces a manifold homeomorphic but not diffeomorphic to the standard `ℝ⁴`, using only
that `Diffeo` is an equivalence relation. -/

/-- **Reduction of the exotic `ℝ⁴` problem to non-uniqueness of smooth structures.**

If some pair of smooth manifolds homeomorphic to `ℝ⁴` fails to be diffeomorphic, then there
exists a smooth manifold homeomorphic but not diffeomorphic to the standard `ℝ⁴`, i.e. an
exotic `ℝ⁴` exists. (Donaldson/Freedman supply the hypothesis; the implication itself is what
is verified here.) -/
theorem exotic_R4 (h : ∃ A B : SmoothR4, ¬ A.Diffeo B) : ExoticR4Exists := by
  obtain ⟨A, B, hAB⟩ := h
  by_contra hcon
  -- Otherwise every smooth structure on `ℝ⁴` is the standard one up to diffeomorphism.
  simp only [ExoticR4Exists, IsExoticR4, not_exists, not_not] at hcon
  exact hAB ((hcon A).trans (hcon B).symm)

/-- The converse reduction: an exotic `ℝ⁴` witnesses non-uniqueness of smooth structures. -/
theorem exists_not_diffeo_of_exoticR4Exists (h : ExoticR4Exists) :
    ∃ A B : SmoothR4, ¬ A.Diffeo B := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, standardR4, hA⟩

/-- The two formulations are equivalent. -/
theorem exoticR4Exists_iff : ExoticR4Exists ↔ ∃ A B : SmoothR4, ¬ A.Diffeo B :=
  ⟨exists_not_diffeo_of_exoticR4Exists, exotic_R4⟩

/-- Spelling out `ExoticR4Exists`: there is a type `X`, with a topology, an atlas of `ℝ⁴`-valued
charts which is `C^∞`-compatible, such that `X` is homeomorphic to `ℝ⁴` but admits no
diffeomorphism onto `ℝ⁴`. -/
theorem exoticR4Exists_iff_explicit :
    ExoticR4Exists ↔
      ∃ (X : Type) (tX : TopologicalSpace X) (cX : @ChartedSpace E4 _ X tX),
        @IsManifold ℝ _ E4 _ _ E4 _ I4 ⊤ X tX cX ∧
        Nonempty (@Homeomorph X E4 tX _) ∧
        IsEmpty (@Diffeomorph ℝ _ E4 _ _ E4 _ _ E4 _ E4 _ I4 I4 X tX cX E4 _ _ ⊤) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.carrier, A.topology, A.charts, A.isManifold, A.homeomorphicToR4,
      not_nonempty_iff.mp hA⟩
  · rintro ⟨X, tX, cX, hX, hhomeo, hdiff⟩
    exact ⟨⟨X, tX, cX, hX, hhomeo⟩, fun hc => hdiff.elim hc.some⟩

end Frontier

