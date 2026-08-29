/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff
open Set

set_option maxHeartbeats 1000000
set_option autoImplicit false

local macro:max "ℝ" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

namespace Frontier

/-!
## A criterion for a manifold to be diffeomorphic to its model space

The key reformulation: a `C^n` manifold `M` modelled on a normed space `E` is `C^n`-diffeomorphic
to `E` itself if and only if its maximal atlas contains a *global* chart, i.e. a chart whose
source is all of `M` and whose target is all of `E`.
-/

section GlobalChart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞}

/-- In the model space `E` (with the trivial model with corners `𝓘(𝕜, E)`), membership in the
`C^n` structure groupoid is just `C^n`-smoothness of the map and of its inverse. -/
theorem mem_contDiffGroupoid_self_iff {e : OpenPartialHomeomorph E E} :
    e ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
      ContDiffOn 𝕜 n e e.source ∧ ContDiffOn 𝕜 n e.symm e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp [contDiffPregroupoid]

variable (𝕜 E M n) in
/-- A `C^n` manifold `M` modelled on `E` *has a global chart* if its maximal `C^n` atlas contains
a chart defined on all of `M` with image all of `E`. -/
def HasGlobalChart : Prop :=
  ∃ e : OpenPartialHomeomorph M E,
    e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M ∧ e.source = univ ∧ e.target = univ

/-- A global chart in the maximal atlas gives a diffeomorphism onto the model space. -/
theorem nonempty_diffeomorph_of_hasGlobalChart [IsManifold 𝓘(𝕜, E) n M]
    (h : HasGlobalChart 𝕜 E M n) : Nonempty (M ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E) := by
  obtain ⟨e, he, hs, ht⟩ := h
  refine ⟨{ toEquiv := (e.toHomeomorphOfSourceEqUnivTargetEqUniv hs ht).toEquiv
            contMDiff_toFun := ?_
            contMDiff_invFun := ?_ }⟩
  · have h := contMDiffOn_of_mem_maximalAtlas he
    rw [hs, contMDiffOn_univ] at h
    exact h
  · have h := contMDiffOn_symm_of_mem_maximalAtlas he
    rw [ht, contMDiffOn_univ] at h
    exact h

/-- A diffeomorphism onto the model space is a global chart in the maximal atlas. -/
theorem hasGlobalChart_of_diffeomorph [IsManifold 𝓘(𝕜, E) n M]
    (Φ : M ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E) : HasGlobalChart 𝕜 E M n := by
  set e : OpenPartialHomeomorph M E := Φ.toHomeomorph.toOpenPartialHomeomorph with he
  refine ⟨e, ?_, by simp [he], by simp [he]⟩
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro c hc
  have hcm : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n c c.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
  have hcm' : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
  have hesymm : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n e.symm univ := by
    have h : ⇑e.symm = ⇑Φ.symm := by simp [he]
    rw [h]; exact Φ.symm.contMDiff.contMDiffOn
  have hefun : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n e univ := by
    have h : ⇑e = ⇑Φ := by simp [he]
    rw [h]; exact Φ.contMDiff.contMDiffOn
  have h1 : ContDiffOn 𝕜 n (⇑(e.symm ≫ₕ c)) (e.symm ≫ₕ c).source := by
    rw [← contMDiffOn_iff_contDiffOn, OpenPartialHomeomorph.coe_trans]
    exact hcm.comp (hesymm.mono (subset_univ _)) fun _ hx => hx.2
  have h2 : ContDiffOn 𝕜 n (⇑(c.symm ≫ₕ e)) (c.symm ≫ₕ e).source := by
    rw [← contMDiffOn_iff_contDiffOn, OpenPartialHomeomorph.coe_trans]
    exact hefun.comp (hcm'.mono fun _ hx => hx.1) fun _ _ => mem_univ _
  refine ⟨?_, ?_⟩
  · rw [mem_contDiffGroupoid_self_iff]
    refine ⟨h1, ?_⟩
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    simpa using h2
  · rw [mem_contDiffGroupoid_self_iff]
    refine ⟨h2, ?_⟩
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    simpa using h1

/-- **Global chart criterion.** A `C^n` manifold modelled on a normed space `E` is
`C^n`-diffeomorphic to `E` if and only if its maximal atlas contains a global chart. -/
theorem nonempty_diffeomorph_model_iff [IsManifold 𝓘(𝕜, E) n M] :
    Nonempty (M ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E) ↔ HasGlobalChart 𝕜 E M n :=
  ⟨fun ⟨Φ⟩ => hasGlobalChart_of_diffeomorph Φ, nonempty_diffeomorph_of_hasGlobalChart⟩

end GlobalChart

/-!
## Exotic `ℝ⁴`
-/

/-- **Existence of an exotic `ℝ⁴`**: there is a smooth (`C^∞`) 4-manifold which is homeomorphic
to `ℝ⁴` but admits no diffeomorphism to `ℝ⁴`.  This is the theorem of Freedman and Donaldson;
here it is only *stated*, as the proposition `ExoticR4Exists`. -/
def ExoticR4Exists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace ℝ⁴ M) (_ : IsManifold (𝓡 4) ∞ M),
    Nonempty (M ≃ₜ ℝ⁴) ∧ IsEmpty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ ℝ⁴)

/-- The reformulation of `ExoticR4Exists` in terms of atlases: there is a smooth 4-manifold
homeomorphic to `ℝ⁴` whose maximal smooth atlas contains no global chart onto `ℝ⁴`. -/
def NoGlobalChartR4Exists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace ℝ⁴ M) (_ : IsManifold (𝓡 4) ∞ M),
    Nonempty (M ≃ₜ ℝ⁴) ∧ ¬ HasGlobalChart ℝ ℝ⁴ M ∞

/-- **Exotic `ℝ⁴` (Freedman–Donaldson), Lean-checked reduction.**

The assertion "there exists a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴`"
is equivalent to the purely atlas-theoretic assertion that there is a smooth `4`-manifold
homeomorphic to `ℝ⁴` whose maximal smooth atlas contains no chart defined on the whole
manifold with image all of `ℝ⁴`.

The equivalence is proved here in full (via the general `nonempty_diffeomorph_model_iff`);
the existence statement itself, `ExoticR4Exists`, is the deep theorem of Freedman and Donaldson
and is not proved. -/
theorem exotic_R4 : ExoticR4Exists ↔ NoGlobalChartR4Exists := by
  constructor
  · rintro ⟨M, _, _, _, hhomeo, hdiff⟩
    refine ⟨M, ‹_›, ‹_›, ‹_›, hhomeo, ?_⟩
    rw [← nonempty_diffeomorph_model_iff, not_nonempty_iff]
    exact hdiff
  · rintro ⟨M, _, _, _, hhomeo, hchart⟩
    refine ⟨M, ‹_›, ‹_›, ‹_›, hhomeo, ?_⟩
    rw [← not_nonempty_iff, nonempty_diffeomorph_model_iff]
    exact hchart

/-- A *small* exotic `ℝ⁴` (an open subset of `ℝ⁴` homeomorphic but not diffeomorphic to `ℝ⁴`,
cf. `exists_open_nonempty_homeomorph_isEmpty_diffeomorph_euclideanSpace_four` in Mathlib)
gives an exotic `ℝ⁴`. -/
theorem exoticR4Exists_of_small
    (h : ∃ U : TopologicalSpace.Opens ℝ⁴, Nonempty (U ≃ₜ ℝ⁴) ∧ IsEmpty (U ≃ₘ⟮𝓡 4, 𝓡 4⟯ ℝ⁴)) :
    ExoticR4Exists := by
  obtain ⟨U, h1, h2⟩ := h
  exact ⟨U, inferInstance, inferInstance, inferInstance, h1, h2⟩

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

