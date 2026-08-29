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
