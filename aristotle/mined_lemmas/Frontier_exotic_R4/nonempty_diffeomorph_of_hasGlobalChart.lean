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
