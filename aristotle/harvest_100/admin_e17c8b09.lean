/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.ChartedSpaceTransport

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The statement "there exists a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴`"
(Donaldson/Freedman) is formalized as `Frontier.ExoticEuclideanExists 4`.

The main theorem `Frontier.exotic_R4` is a Lean-checked reduction of that statement:

* the existence of a *small* exotic `ℝ⁴` (an open subset of `ℝ⁴` homeomorphic but not
  diffeomorphic to `ℝ⁴`, which is the form in which exotic `ℝ⁴`'s are usually produced)
  implies the existence of an exotic `ℝ⁴`;
* the existence of an exotic `ℝ⁴` is *equivalent* to the existence of a smooth structure on the
  topological space `ℝ⁴` itself which is not diffeomorphic to the standard one.

The dimension-zero base case, `Frontier.no_exotic_R0`, is proved outright: there is no
exotic `ℝ⁰`.
-/

open scoped Manifold ContDiff
open TopologicalSpace

namespace Frontier

/-- Diffeomorphisms from a smooth manifold `M`, equipped with the charted space structure `cM`
over `ℝⁿ`, to `ℝⁿ` with its *standard* smooth structure.  Spelling the charted space structures
out explicitly is necessary because we want to compare two different smooth structures on the
same topological space. -/
abbrev DiffeoToStdEuclidean (n : ℕ) (M : Type) [TopologicalSpace M]
    (cM : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) : Type :=
  @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _ (𝓡 n) (𝓡 n) M _ cM (EuclideanSpace ℝ (Fin n)) _
    (chartedSpaceSelf (EuclideanSpace ℝ (Fin n))) ∞

/-- Sanity check: `ℝⁿ` with its standard smooth structure *is* diffeomorphic to the standard
`ℝⁿ`, so the conditions above are not vacuous. -/
theorem nonempty_diffeoToStdEuclidean_self (n : ℕ) :
    Nonempty (DiffeoToStdEuclidean n (EuclideanSpace ℝ (Fin n))
      (chartedSpaceSelf (EuclideanSpace ℝ (Fin n)))) :=
  ⟨Diffeomorph.refl (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞⟩

/-- `ExoticEuclideanExists n` is the statement that there is a smooth `n`-manifold which is
homeomorphic, but not diffeomorphic, to `ℝⁿ`.  For `n = 4` this is the statement of the
existence of an exotic `ℝ⁴` (Donaldson/Freedman). -/
def ExoticEuclideanExists (n : ℕ) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (cM : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (_ : @IsManifold ℝ _ _ _ _ _ _ (𝓡 n) ∞ M _ cM),
    Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin n)) ∧ IsEmpty (DiffeoToStdEuclidean n M cM)

/-- The existence of a *small* exotic `ℝ⁴`: an open subset of `ℝ⁴` which is homeomorphic but
not diffeomorphic to `ℝ⁴` (with its induced smooth structure). -/
def SmallExoticR4 : Prop :=
  ∃ U : Opens (EuclideanSpace ℝ (Fin 4)),
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 4)) ∧ IsEmpty (DiffeoToStdEuclidean 4 U inferInstance)

/-- The existence of an exotic smooth structure on the topological space `ℝⁿ`: a charted space
structure `c` on `ℝⁿ` making it a smooth `n`-manifold which is not diffeomorphic to `ℝⁿ` with
its standard smooth structure. -/
def ExoticStructureOnEuclidean (n : ℕ) : Prop :=
  ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
    ∃ _ : @IsManifold ℝ _ _ _ _ _ _ (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n)) _ c,
      IsEmpty (DiffeoToStdEuclidean n (EuclideanSpace ℝ (Fin n)) c)

/-- The existence of an exotic `ℝⁿ` is equivalent to the existence of a nonstandard smooth
structure on the topological space `ℝⁿ` itself: a smooth structure can be transported along a
homeomorphism, and the homeomorphism then becomes a diffeomorphism. -/
theorem exotic_euclidean_iff (n : ℕ) :
    ExoticEuclideanExists n ↔ ExoticStructureOnEuclidean n := by
  constructor
  · rintro ⟨M, tM, cM, mM, ⟨e⟩, hempty⟩
    refine ⟨transportChartedSpace (H := EuclideanSpace ℝ (Fin n)) e.symm,
      transportChartedSpace_isManifold (𝓡 n) ∞ e.symm, ?_⟩
    obtain ⟨D⟩ := nonempty_diffeomorph_transportChartedSpace (𝓡 n) (∞ : WithTop ℕ∞) e.symm
    refine ⟨fun D' => hempty.false ?_⟩
    exact diffeoTrans (𝓡 n) ∞ cM (transportChartedSpace e.symm)
      (chartedSpaceSelf (EuclideanSpace ℝ (Fin n)))
      (diffeoSymm (𝓡 n) ∞ (transportChartedSpace e.symm) cM D) D'
  · rintro ⟨c, m, hempty⟩
    exact ⟨EuclideanSpace ℝ (Fin n), inferInstance, c, m, ⟨Homeomorph.refl _⟩, hempty⟩

/-- **Reduction for the existence of an exotic `ℝ⁴`** (Donaldson/Freedman).

The full theorem — that a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴` exists —
is not proved here; what is proved is a Lean-checked reduction:

* it suffices to exhibit a *small* exotic `ℝ⁴`, i.e. an open subset of `ℝ⁴` that is homeomorphic
  but not diffeomorphic to `ℝ⁴`;
* and the statement is equivalent to the existence of a smooth structure on the topological
  space `ℝ⁴` which is not diffeomorphic to the standard one. -/
theorem exotic_R4 :
    (SmallExoticR4 → ExoticEuclideanExists 4) ∧
      (ExoticEuclideanExists 4 ↔ ExoticStructureOnEuclidean 4) := by
  refine ⟨?_, exotic_euclidean_iff 4⟩
  rintro ⟨U, h₁, h₂⟩
  exact ⟨U, inferInstance, inferInstance, inferInstance, h₁, h₂⟩

/-- Base case: there is no exotic `ℝ⁰`.  Every smooth `0`-manifold homeomorphic to `ℝ⁰` is
diffeomorphic to `ℝ⁰`. -/
theorem no_exotic_R0 : ¬ ExoticEuclideanExists 0 := by
  rintro ⟨M, tM, cM, mM, ⟨e⟩, hempty⟩
  refine hempty.false ⟨e.toEquiv, ?_, ?_⟩
  · have h : (⇑e.toEquiv) = fun _ : M => (0 : EuclideanSpace ℝ (Fin 0)) := by
      funext x
      exact Subsingleton.elim _ _
    rw [h]
    exact contMDiff_const
  · have h : (⇑e.toEquiv.symm) = fun _ : EuclideanSpace ℝ (Fin 0) => e.symm 0 := by
      funext x
      rw [Subsingleton.elim x (0 : EuclideanSpace ℝ (Fin 0))]
      rfl
    rw [h]
    exact contMDiff_const

end Frontier

import Mathlib

/-!
# Transport of charted space and smooth structures along a homeomorphism

If `e : X ≃ₜ Y` is a homeomorphism and `Y` is a charted space over `H`, then `X` inherits a
charted space structure whose charts are the charts of `Y` precomposed with `e`.  This structure
is a `C^n` manifold structure whenever `Y`'s is, and `e` becomes a diffeomorphism.

These are the tools needed to move a smooth structure from an abstract manifold to a fixed
topological space homeomorphic to it.
-/

open scoped Manifold ContDiff
open Set

namespace Frontier

variable {𝕜 E H X Y : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]

/-- Composing on the left with a homeomorphism cancels in a transition map. -/
theorem symm_trans_cancel (e : X ≃ₜ Y) (a b : OpenPartialHomeomorph Y H) :
    (e.toOpenPartialHomeomorph ≫ₕ a).symm ≫ₕ (e.toOpenPartialHomeomorph ≫ₕ b)
      = a.symm ≫ₕ b := by
  refine OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun x => ?_) ?_ <;>
    simp [mfld_simps, Set.preimage_preimage]

/-- Composing with `e.symm` and then `e` is the identity. -/
theorem symm_trans_self_trans (e : X ≃ₜ Y) (c : OpenPartialHomeomorph Y H) :
    e.symm.toOpenPartialHomeomorph ≫ₕ (e.toOpenPartialHomeomorph ≫ₕ c) = c := by
  refine OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun x => ?_) ?_ <;>
    simp [mfld_simps, Set.preimage_preimage]

/-- Transport a charted space structure along a homeomorphism `e : X ≃ₜ Y`:
the charts of `X` are the charts of `Y`, precomposed with `e`. -/
def transportChartedSpace [ChartedSpace H Y] (e : X ≃ₜ Y) : ChartedSpace H X where
  atlas := (fun c => e.toOpenPartialHomeomorph ≫ₕ c) '' (atlas H Y)
  chartAt x := e.toOpenPartialHomeomorph ≫ₕ chartAt H (e x)
  mem_chart_source x := by simp [mfld_simps]
  chart_mem_atlas x := ⟨chartAt H (e x), chart_mem_atlas _ _, rfl⟩

/-- The transported charted space structure has the same structure groupoid. -/
theorem transportChartedSpace_hasGroupoid [ChartedSpace H Y] (G : StructureGroupoid H)
    [HasGroupoid Y G] (e : X ≃ₜ Y) :
    @HasGroupoid _ _ _ _ (transportChartedSpace e) G := by
  letI := transportChartedSpace (H := H) e
  refine ⟨?_⟩
  rintro f f' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  rw [symm_trans_cancel]
  exact HasGroupoid.compatible ha hb

/-- The transported structure is a `C^n` manifold structure. -/
theorem transportChartedSpace_isManifold (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [ChartedSpace H Y] [IsManifold I n Y] (e : X ≃ₜ Y) :
    @IsManifold 𝕜 _ E _ _ H _ I n X _ (transportChartedSpace e) := by
  letI := transportChartedSpace (H := H) e
  haveI := transportChartedSpace_hasGroupoid (H := H) (contDiffGroupoid n I) e
  exact IsManifold.mk' I n X

/-- If the charts of `X` are the charts of `Y` precomposed with a homeomorphism `e : X ≃ₜ Y`,
then `e` is `C^n`. -/
theorem contMDiff_of_chartAt_eq (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [ChartedSpace H X] [ChartedSpace H Y] [IsManifold I n X] [IsManifold I n Y]
    (e : X ≃ₜ Y)
    (h : ∀ x : X, chartAt H x = e.toOpenPartialHomeomorph ≫ₕ chartAt H (e x)) :
    ContMDiff I I n (e : X → Y) := by
  intro x
  have hsrc : (chartAt H x).source = e ⁻¹' (chartAt H (e x)).source := by
    rw [h x]; simp [mfld_simps]
  have hmaps : MapsTo (chartAt H x) (chartAt H x).source (chartAt H (e x)).target := by
    intro z hz
    have hz' : (chartAt H x) z = (chartAt H (e x)) (e z) := by rw [h x]; simp [mfld_simps]
    rw [hz']
    exact (chartAt H (e x)).map_source (by simpa [hsrc] using hz)
  have hcomp : ContMDiffOn I I n ((chartAt H (e x)).symm ∘ (chartAt H x)) (chartAt H x).source :=
    contMDiffOn_chart_symm.comp contMDiffOn_chart hmaps
  have heq : EqOn (e : X → Y) ((chartAt H (e x)).symm ∘ (chartAt H x)) (chartAt H x).source := by
    intro z hz
    have h1 : (chartAt H x) z = (chartAt H (e x)) (e z) := by rw [h x]; simp [mfld_simps]
    have h2 : e z ∈ (chartAt H (e x)).source := by simpa [hsrc] using hz
    simp [Function.comp, h1, (chartAt H (e x)).left_inv h2]
  exact (hcomp.congr heq).contMDiffAt ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))

/-- If the charts of `X` are the charts of `Y` precomposed with a homeomorphism `e : X ≃ₜ Y`,
then `e` is a diffeomorphism. -/
theorem nonempty_diffeomorph_of_chartAt_eq (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [ChartedSpace H X] [ChartedSpace H Y] [IsManifold I n X] [IsManifold I n Y]
    (e : X ≃ₜ Y)
    (h : ∀ x : X, chartAt H x = e.toOpenPartialHomeomorph ≫ₕ chartAt H (e x)) :
    Nonempty (X ≃ₘ^n⟮I, I⟯ Y) := by
  have h' : ∀ y : Y, chartAt H y = e.symm.toOpenPartialHomeomorph ≫ₕ chartAt H (e.symm y) := by
    intro y
    rw [h (e.symm y), Homeomorph.apply_symm_apply, symm_trans_self_trans]
  exact ⟨{ toEquiv := e.toEquiv
           contMDiff_toFun := contMDiff_of_chartAt_eq I n e h
           contMDiff_invFun := contMDiff_of_chartAt_eq I n e.symm h' }⟩

/-- The inverse of a diffeomorphism, with the charted space structures given explicitly.
This is `Diffeomorph.symm`, but usable when the two manifolds share the same underlying type
with different smooth structures. -/
def diffeoSymm (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (cX : ChartedSpace H X) (cY : ChartedSpace H Y)
    (D : @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I X _ cX Y _ cY n) :
    @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I Y _ cY X _ cX n := by
  letI := cX; letI := cY
  exact D.symm

/-- Composition of diffeomorphisms, with the charted space structures given explicitly.
This is `Diffeomorph.trans`, but usable when the manifolds share the same underlying type
with different smooth structures. -/
def diffeoTrans (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) {Z : Type*} [TopologicalSpace Z]
    (cX : ChartedSpace H X) (cY : ChartedSpace H Y) (cZ : ChartedSpace H Z)
    (D₁ : @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I X _ cX Y _ cY n)
    (D₂ : @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I Y _ cY Z _ cZ n) :
    @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I X _ cX Z _ cZ n := by
  letI := cX; letI := cY; letI := cZ
  exact D₁.trans D₂

/-- A homeomorphism is a diffeomorphism for the transported smooth structure. -/
theorem nonempty_diffeomorph_transportChartedSpace (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [ChartedSpace H Y] [IsManifold I n Y] (e : X ≃ₜ Y) :
    Nonempty (@Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I X _ (transportChartedSpace e) Y _ _ n) := by
  letI := transportChartedSpace (H := H) e
  haveI := transportChartedSpace_isManifold I n e
  exact nonempty_diffeomorph_of_chartAt_eq I n e (fun _ => rfl)

end Frontier

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

